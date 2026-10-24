#!/usr/bin/env bash
# Manage isolated git worktrees under .worktrees/ with shared read-only dependency packages
# and pre-bootstrapped caches.
#
# Usage:
#   scripts/worktree.sh create <branch> [dir_name] [base_ref] [--copy-cslib | --copy-packages]
#                              [--force-reset]
#   scripts/worktree.sh seed <worktree_path> [--copy-cslib | --copy-packages]
#   scripts/worktree.sh list
#   scripts/worktree.sh prune-merged [base_ref] [--dry-run]
#
# Branch selection for `create`:
#   * an existing local branch is checked out as is (`--force-reset` resets it to base_ref);
#   * a branch that exists only on `origin` (the usual takeover case) is created locally tracking
#     `origin/<branch>`, after fetching it; passing base_ref for such a branch is refused, because
#     it would silently discard the pushed work (`--force-reset` overrides the refusal; without a
#     base_ref, `--force-reset` still tracks `origin/<branch>` rather than discarding it). If the
#     fetch fails (offline, or the branch was deleted on origin), the local `origin/<branch>` ref,
#     possibly stale, is used when present;
#   * otherwise a new branch is created from base_ref (default `origin/main`) without upstream
#     tracking, so a plain `git push` cannot target the base branch.
#
# Cache seeding and bootstrap note:
#   By default, `.lake/packages` in a worktree is linked to a read-only, pin-keyed shared directory
#   (`.worktrees/.shared/packages-cslib-<rev>`, or an existing `.shared/packages-cslib-<rev>`
#   alongside the worktree). When the pin in `lake-manifest.json` changes, a new
#   `packages-cslib-<rev>` directory is created; an existing shared directory is never updated in
#   place. A worktree is never pointed at the primary checkout, and seeding refuses the primary
#   checkout or any symlink into it. `--copy-cslib` creates a writable copy of `cslib` while
#   linking the other packages to the shared directory; `--copy-packages` creates writable copies
#   of all packages. After seeding, `create` and `seed` run `scripts/cache/ensure.sh` (or
#   `scripts/cache/get.sh`) when present in the worktree unless `COMPLEXITYLIB_CACHE_AUTO=0`.
#
# Pruning considers registered worktrees directly under `.worktrees/`, retaining locked,
# symlinked, dirty and unmerged worktrees. Git removes eligible worktrees and their caches.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
GIT_COMMON_DIR="$(git -C "$SCRIPT_DIR" rev-parse --path-format=absolute --git-common-dir)"
ROOT="$(cd "$GIT_COMMON_DIR/.." && pwd)"
cd "$ROOT"

# seed_package <source> <destination> <copy_sources>. Copy caches without first hard-linking them.
seed_package() (
  local source="$1" destination="$2" copy_sources="$3" entry
  mkdir -p "$destination"
  shopt -s dotglob nullglob
  for entry in "$source"/*; do
    if [ "$(basename "$entry")" = ".lake" ]; then
      cp -aL "$entry" "$destination/.lake"
    elif [ "$copy_sources" = "true" ]; then
      cp -a "$entry" "$destination/"
    else
      cp -al "$entry" "$destination/"
    fi
  done
)

# resolve_shared_packages_dir <worktree_path>: print the path to the pin-keyed shared packages
# directory (e.g. `.worktrees/.shared/packages-cslib-<rev>`), or fail if
# COMPLEXITYLIB_SHARED_PACKAGES_ROOT points into the primary checkout.
resolve_shared_packages_dir() {
  local wt_path="$1"
  python3 - "$ROOT" "$wt_path" <<'PY'
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

root = Path(sys.argv[1]).resolve()
wt_path = Path(sys.argv[2])
worktrees_root = (root / ".worktrees").resolve()


def in_primary_checkout(p: Path) -> bool:
    return p == root or (p.is_relative_to(root) and not p.is_relative_to(worktrees_root))


manifest = wt_path / "lake-manifest.json"
if not manifest.is_file():
    manifest = root / "lake-manifest.json"

pin_name = None
if manifest.is_file():
    try:
        data = json.loads(manifest.read_text(encoding="utf-8"))
        for pkg in data.get("packages", []):
            if isinstance(pkg, dict) and pkg.get("name") == "cslib":
                rev = pkg.get("rev") or ""
                if isinstance(rev, str) and rev:
                    pin_name = f"packages-cslib-{rev[:8]}"
                    break
    except (OSError, ValueError, TypeError):
        pass

if pin_name is None:
    cslib_dir = root / ".lake/packages/cslib"
    if (cslib_dir / ".git").exists():
        try:
            rev = subprocess.check_output(
                ["git", "-C", str(cslib_dir), "rev-parse", "--short=8", "HEAD"],
                text=True,
                stderr=subprocess.DEVNULL,
            ).strip()
            if rev:
                pin_name = f"packages-cslib-{rev}"
        except (OSError, subprocess.CalledProcessError):
            pass

if pin_name is None:
    if manifest.is_file():
        digest = hashlib.sha256(manifest.read_bytes()).hexdigest()[:8]
        pin_name = f"packages-manifest-{digest}"
    else:
        pin_name = "packages-cslib-default"

env_shared = os.environ.get("COMPLEXITYLIB_SHARED_PACKAGES_ROOT", "")
if env_shared:
    shared_root = Path(env_shared).resolve()
    if in_primary_checkout(shared_root) or shared_root == worktrees_root:
        print(
            f"Refusing shared packages directory inside primary checkout: {env_shared}",
            file=sys.stderr,
        )
        raise SystemExit(1)
    print(shared_root / pin_name)
    raise SystemExit(0)

candidates = []
try:
    wt_parent = wt_path.resolve().parent
    if not in_primary_checkout(wt_parent) and wt_parent != worktrees_root:
        candidates.append(wt_parent / ".shared" / pin_name)
except OSError:
    pass
candidates.append(worktrees_root / ".shared" / pin_name)
candidates.append(Path(f"{root}-wt") / ".shared" / pin_name)

for cand in candidates:
    if cand.is_dir() and not in_primary_checkout(cand.resolve()):
        print(cand)
        raise SystemExit(0)

print(worktrees_root / ".shared" / pin_name)
PY
}

# check_worktree_safety <worktree_path> <expected_shared_pkg_dir>: refuse if the target worktree
# is the primary checkout or contains symlinks pointing into the primary checkout or unexpected
# external cache directories.
check_worktree_safety() {
  local wt_path="$1"
  local expected_shared="$2"
  python3 - "$ROOT" "$wt_path" "$expected_shared" <<'PY'
from pathlib import Path
import sys

root = Path(sys.argv[1]).resolve()
wt_raw = Path(sys.argv[2])
expected_shared = Path(sys.argv[3]).resolve() if sys.argv[3] else None
worktrees_root = (root / ".worktrees").resolve()


def in_primary_checkout(p: Path) -> bool:
    return p == root or (p.is_relative_to(root) and not p.is_relative_to(worktrees_root))


if wt_raw.is_symlink():
    target = wt_raw.resolve()
    if in_primary_checkout(target):
        print(
            f"Refusing worktree symlink pointing into primary checkout: {wt_raw} -> {target}",
            file=sys.stderr,
        )
        raise SystemExit(1)

wt_real = wt_raw.resolve()
if in_primary_checkout(wt_real):
    print(f"Refusing to seed or point at primary checkout: {wt_raw}", file=sys.stderr)
    raise SystemExit(1)

if expected_shared is not None and in_primary_checkout(expected_shared):
    print(
        f"Refusing shared packages directory inside primary checkout: {expected_shared}",
        file=sys.stderr,
    )
    raise SystemExit(1)

for rel in (".lake", ".lake/build", ".lake/config"):
    cand = wt_raw / rel
    if cand.is_symlink():
        target = cand.resolve()
        if in_primary_checkout(target):
            print(
                f"Refusing destination cache symlink pointing into primary checkout: {cand} -> {target}",
                file=sys.stderr,
            )
        else:
            print(f"Refusing to seed through destination cache symlink: {cand}", file=sys.stderr)
        raise SystemExit(1)

pkg_link = wt_raw / ".lake/packages"
if pkg_link.is_symlink():
    target = pkg_link.resolve()
    if in_primary_checkout(target):
        print(
            f"Refusing destination cache symlink pointing into primary checkout: {pkg_link} -> {target}",
            file=sys.stderr,
        )
        raise SystemExit(1)
    if expected_shared is None or target != expected_shared:
        print(f"Refusing to seed through destination cache symlink: {pkg_link}", file=sys.stderr)
        raise SystemExit(1)
elif pkg_link.is_dir():
    for child in pkg_link.iterdir():
        if child.is_symlink():
            target = child.resolve()
            if in_primary_checkout(target):
                print(
                    f"Refusing package symlink pointing into primary checkout: {child} -> {target}",
                    file=sys.stderr,
                )
                raise SystemExit(1)
            if expected_shared is None or target != (expected_shared / child.name).resolve():
                print(
                    f"Refusing to seed through destination cache symlink: {child}",
                    file=sys.stderr,
                )
                raise SystemExit(1)
PY
}

# root_packages_match_manifest <worktree_path>: return 0 unless both the target manifest pins a
# cslib git revision and $ROOT/.lake/packages/cslib is a git checkout at a different revision.
root_packages_match_manifest() {
  local wt_path="$1"
  python3 - "$ROOT" "$wt_path" <<'PY'
import json
from pathlib import Path
import subprocess
import sys

root = Path(sys.argv[1]).resolve()
wt_path = Path(sys.argv[2])
cslib_git = root / ".lake/packages/cslib/.git"
manifest = wt_path / "lake-manifest.json"
if not manifest.is_file():
    manifest = root / "lake-manifest.json"
if not cslib_git.exists() or not manifest.is_file():
    raise SystemExit(0)

try:
    data = json.loads(manifest.read_text(encoding="utf-8"))
    manifest_rev = None
    for pkg in data.get("packages", []):
        if isinstance(pkg, dict) and pkg.get("name") == "cslib":
            manifest_rev = pkg.get("rev")
            break
    if not manifest_rev:
        raise SystemExit(0)
    actual_rev = subprocess.check_output(
        ["git", "-C", str(cslib_git.parent), "rev-parse", "HEAD"],
        text=True,
        stderr=subprocess.DEVNULL,
    ).strip()
    if actual_rev and not actual_rev.startswith(manifest_rev[:8]) and not manifest_rev.startswith(actual_rev[:8]):
        print(
            f"Root .lake/packages/cslib ({actual_rev[:8]}) does not match manifest pin ({manifest_rev[:8]}); skipping mismatched package seed.",
            file=sys.stderr,
        )
        raise SystemExit(1)
except (OSError, ValueError, TypeError, subprocess.CalledProcessError):
    pass
PY
}

# ensure_shared_packages <worktree_path> <shared_pkg_dir>: create <shared_pkg_dir> once as an
# isolated read-only copy of $ROOT/.lake/packages when not already present; never update in place.
ensure_shared_packages() {
  local wt_path="$1"
  local shared_pkg_dir="$2"
  if [ -d "$shared_pkg_dir" ]; then
    return 0
  fi
  if [ ! -d "$ROOT/.lake/packages" ]; then
    return 0
  fi
  if ! root_packages_match_manifest "$wt_path"; then
    return 0
  fi
  mkdir -p "$(dirname "$shared_pkg_dir")"
  local staging
  staging="$(mktemp -d "$(dirname "$shared_pkg_dir")/.staging-$(basename "$shared_pkg_dir").XXXXXX")"
  local pkg name
  for pkg in "$ROOT"/.lake/packages/*; do
    [ -d "$pkg" ] || continue
    name="$(basename "$pkg")"
    seed_package "$pkg" "$staging/$name" "true"
  done
  find "$staging" -type f -exec chmod a-w {} +
  if ! python3 - "$staging" "$shared_pkg_dir" <<'PY'
import os
from pathlib import Path
import shutil
import sys

staging = Path(sys.argv[1])
target = Path(sys.argv[2])
if target.exists():
    shutil.rmtree(staging)
else:
    try:
        os.rename(staging, target)
    except OSError:
        shutil.rmtree(staging)
        if not target.exists():
            raise
PY
  then
    rm -rf "$staging"
    return 1
  fi
}

# bootstrap_cache <worktree_path>: run scripts/cache/ensure.sh (or scripts/cache/get.sh) in the
# worktree when present unless COMPLEXITYLIB_CACHE_AUTO=0.
bootstrap_cache() {
  local wt_path="$1"
  if [ "${COMPLEXITYLIB_CACHE_AUTO:-1}" = "0" ]; then
    return 0
  fi
  if [ -x "$wt_path/scripts/cache/ensure.sh" ]; then
    "$wt_path/scripts/cache/ensure.sh"
  elif [ -x "$wt_path/scripts/cache/get.sh" ]; then
    (cd "$wt_path" && scripts/cache/get.sh)
  fi
}

# seed_lake <worktree_path> <copy_mode>, where copy_mode is `none`, `cslib` or `all`.
seed_lake() {
  local wt_path="$1"
  local copy_mode="${2:-none}"
  local shared_pkg_dir
  shared_pkg_dir="$(resolve_shared_packages_dir "$wt_path")"
  check_worktree_safety "$wt_path" "$shared_pkg_dir"
  if [ ! -d "$shared_pkg_dir" ] && [ ! -d "$ROOT/.lake" ]; then
    echo "No root .lake directory found at $ROOT/.lake; skipping cache seed."
    bootstrap_cache "$wt_path"
    return 0
  fi
  mkdir -p "$wt_path/.lake"
  if [ ! -e "$wt_path/.lake/packages" ] && [ ! -L "$wt_path/.lake/packages" ]; then
    if [ "$copy_mode" = "none" ]; then
      ensure_shared_packages "$wt_path" "$shared_pkg_dir"
      if [ -d "$shared_pkg_dir" ]; then
        ln -s "$shared_pkg_dir" "$wt_path/.lake/packages"
      fi
    elif [ "$copy_mode" = "cslib" ]; then
      ensure_shared_packages "$wt_path" "$shared_pkg_dir"
      if [ -d "$shared_pkg_dir" ] || [ -d "$ROOT/.lake/packages" ]; then
        mkdir -p "$wt_path/.lake/packages"
        if [ -d "$ROOT/.lake/packages/cslib" ] && root_packages_match_manifest "$wt_path"; then
          seed_package "$ROOT/.lake/packages/cslib" "$wt_path/.lake/packages/cslib" "true"
        elif [ -d "$shared_pkg_dir/cslib" ]; then
          seed_package "$shared_pkg_dir/cslib" "$wt_path/.lake/packages/cslib" "true"
          chmod -R u+w "$wt_path/.lake/packages/cslib"
        fi
        if [ -d "$shared_pkg_dir" ]; then
          local pkg name
          for pkg in "$shared_pkg_dir"/*; do
            [ -d "$pkg" ] || continue
            name="$(basename "$pkg")"
            [ "$name" = "cslib" ] && continue
            ln -s "$pkg" "$wt_path/.lake/packages/$name"
          done
        fi
      fi
    elif [ "$copy_mode" = "all" ]; then
      if [ -d "$ROOT/.lake/packages" ] && root_packages_match_manifest "$wt_path"; then
        mkdir -p "$wt_path/.lake/packages"
        local pkg name
        for pkg in "$ROOT"/.lake/packages/*; do
          [ -d "$pkg" ] || continue
          name="$(basename "$pkg")"
          seed_package "$pkg" "$wt_path/.lake/packages/$name" "true"
        done
      elif [ -d "$shared_pkg_dir" ]; then
        mkdir -p "$wt_path/.lake/packages"
        local pkg name
        for pkg in "$shared_pkg_dir"/*; do
          [ -d "$pkg" ] || continue
          name="$(basename "$pkg")"
          seed_package "$pkg" "$wt_path/.lake/packages/$name" "true"
          chmod -R u+w "$wt_path/.lake/packages/$name"
        done
      fi
    fi
  fi
  if [ -d "$ROOT/.lake/config" ] && [ ! -d "$wt_path/.lake/config" ]; then
    cp -aL "$ROOT/.lake/config" "$wt_path/.lake/config"
  fi
  if [ -d "$ROOT/.lake/build" ] && [ ! -d "$wt_path/.lake/build" ]; then
    cp -aL "$ROOT/.lake/build" "$wt_path/.lake/build"
  fi
  bootstrap_cache "$wt_path"
}

# copy_mode_flag <current_mode> <arg>: print the new copy mode, or fail on conflicting flags.
copy_mode_flag() {
  local current="$1" requested
  case "$2" in
    --copy-cslib) requested="cslib" ;;
    --copy-packages) requested="all" ;;
  esac
  if [ "$current" != "none" ] && [ "$current" != "$requested" ]; then
    echo "--copy-cslib and --copy-packages are mutually exclusive." >&2
    return 1
  fi
  echo "$requested"
}

cmd="${1:-list}"
shift || true

case "$cmd" in
  create)
    branch="${1:?Usage: scripts/worktree.sh create <branch> [dir_name] [base_ref] [--copy-cslib | --copy-packages] [--force-reset]}"
    shift
    dir_name=""
    base_ref=""
    copy_mode="none"
    force_reset="false"
    for arg in "$@"; do
      if [ "$arg" = "--copy-cslib" ] || [ "$arg" = "--copy-packages" ]; then
        copy_mode="$(copy_mode_flag "$copy_mode" "$arg")"
      elif [ "$arg" = "--force-reset" ]; then
        force_reset="true"
      elif [ -z "$dir_name" ]; then
        dir_name="$arg"
      elif [ -z "$base_ref" ]; then
        base_ref="$arg"
      else
        echo "Unexpected argument: $arg" >&2
        exit 1
      fi
    done
    if [ -z "$dir_name" ]; then
      dir_name="${branch//\//-}"
    fi
    wt_path="$ROOT/.worktrees/$dir_name"
    if git show-ref --verify --quiet "refs/heads/$branch"; then
      if [ "$force_reset" = "true" ]; then
        effective_base="${base_ref:-origin/main}"
        git worktree add -B "$branch" "$wt_path" "$effective_base"
        seed_lake "$wt_path" "$copy_mode"
        echo "Ready: $wt_path (branch $branch reset to $effective_base)"
      else
        if [ -n "$base_ref" ]; then
          echo "Branch '$branch' already exists locally; refusing to reset it to '$base_ref' without --force-reset." >&2
          exit 1
        fi
        git worktree add "$wt_path" "$branch"
        seed_lake "$wt_path" "$copy_mode"
        echo "Ready: $wt_path (existing branch $branch)"
      fi
    else
      # Refresh origin/<branch> so a branch pushed by another worker is not mistaken for a new one.
      # A failed fetch (offline, or no such remote branch) falls back to the local remote refs.
      git fetch --quiet origin "+refs/heads/$branch:refs/remotes/origin/$branch" 2>/dev/null || true
      if git show-ref --verify --quiet "refs/remotes/origin/$branch"; then
        if [ -n "$base_ref" ] && [ "$force_reset" != "true" ]; then
          echo "Branch '$branch' exists on origin; refusing to create it from '$base_ref' (that would discard the pushed work)." >&2
          echo "hint: omit base_ref to track origin/$branch, or pass --force-reset to start '$branch' from '$base_ref' anyway." >&2
          exit 1
        fi
        if [ -n "$base_ref" ]; then
          git worktree add --no-track -b "$branch" "$wt_path" "$base_ref"
          seed_lake "$wt_path" "$copy_mode"
          echo "Ready: $wt_path (new branch $branch from $base_ref; origin/$branch ignored by --force-reset)"
        else
          git worktree add --track -b "$branch" "$wt_path" "origin/$branch"
          seed_lake "$wt_path" "$copy_mode"
          echo "Ready: $wt_path (branch $branch tracking origin/$branch)"
        fi
      else
        effective_base="${base_ref:-origin/main}"
        git worktree add --no-track -b "$branch" "$wt_path" "$effective_base"
        seed_lake "$wt_path" "$copy_mode"
        echo "Ready: $wt_path (new branch $branch from $effective_base)"
      fi
    fi
    ;;
  seed)
    wt_path="${1:?Usage: scripts/worktree.sh seed <worktree_path> [--copy-cslib | --copy-packages]}"
    shift
    copy_mode="none"
    for arg in "$@"; do
      if [ "$arg" = "--copy-cslib" ] || [ "$arg" = "--copy-packages" ]; then
        copy_mode="$(copy_mode_flag "$copy_mode" "$arg")"
      else
        echo "Unexpected argument: $arg" >&2
        exit 1
      fi
    done
    seed_lake "$wt_path" "$copy_mode"
    echo "Seeded .lake cache in $wt_path"
    ;;
  list)
    git worktree list
    ;;
  prune-merged)
    base_ref="origin/main"
    dry_run="false"
    for arg in "$@"; do
      if [ "$arg" = "--dry-run" ]; then
        dry_run="true"
      else
        base_ref="$arg"
      fi
    done
    if [ ! -d "$ROOT/.worktrees" ]; then
      exit 0
    fi
    wt=""
    locked="false"
    # NUL-delimited inventory keeps spaces/newlines in paths and excludes foreign directories.
    git worktree list --porcelain -z | while IFS= read -r -d '' record; do
      case "$record" in
        "worktree "*)
          wt="${record#worktree }"
          locked="false"
          continue
          ;;
        locked|locked\ *) locked="true"; continue ;;
        "") ;;
        *) continue ;;
      esac
      case "$wt" in
        "$ROOT/.worktrees/"*) ;;
        *) continue ;;
      esac
      # Match the former direct-child scope, excluding nested paths and prefix lookalikes.
      case "${wt#"$ROOT/.worktrees/"}" in
        ""|*/*) continue ;;
      esac
      if [ "$locked" = "true" ] || [ -L "$wt" ]; then
        echo "Keeping $wt (locked or symlinked worktree)"
        continue
      fi
      [ -d "$wt" ] || continue
      if [ -n "$(git -C "$wt" status --porcelain)" ]; then
        echo "Keeping $wt (dirty working tree)"
        continue
      fi
      unmerged="$(git -C "$wt" log --oneline "$base_ref..HEAD")"
      if [ -n "$unmerged" ]; then
        echo "Keeping $wt (has unmerged commits)"
        continue
      fi
      if [ "$dry_run" = "true" ]; then
        echo "Would remove merged worktree $wt"
      else
        echo "Removing merged worktree $wt"
        # Git checks registration, locks and cleanliness again before deleting anything.
        git worktree remove "$wt"
      fi
    done
    ;;
  *)
    echo "Unknown command: $cmd" >&2
    exit 1
    ;;
esac
