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
#   (`.worktrees/.shared/packages-cslib-<rev>[-<state>]`, or a verified existing
#   `.shared/packages-cslib-<rev>` alongside the worktree). Both files and directories in the
#   shared pool are read-only so neither in-place writes nor atomic file replacements can mutate
#   shared artifacts across workers. When any dependency pin in `lake-manifest.json` or
#   `lean-toolchain` changes, a new shared directory is created; an existing shared directory is
#   never updated in place. A worktree is never pointed at the primary checkout, and seeding
#   refuses the primary checkout or any symlink into it (and dereferences any package source
#   symlink that would escape the isolated package tree). `--copy-cslib` creates a writable copy of
#   `cslib` while linking the other packages to the shared directory; `--copy-packages` creates
#   writable copies of all packages. After seeding, `create` and `seed` run
#   `scripts/cache/ensure.sh` (or `scripts/cache/get.sh`) when present in the worktree unless
#   `COMPLEXITYLIB_CACHE_AUTO=0`.
#
# Pruning considers registered worktrees directly under `.worktrees/`, retaining locked,
# symlinked, dirty and unmerged worktrees. Git removes eligible worktrees and their caches.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
GIT_COMMON_DIR="$(git -C "$SCRIPT_DIR" rev-parse --path-format=absolute --git-common-dir)"
ROOT="$(cd "$GIT_COMMON_DIR/.." && pwd)"
cd "$ROOT"

# seed_package <source> <destination> <copy_sources>. Copy caches without first hard-linking them,
# and materialize any source symlink whose raw target is absolute or resolves outside <destination>
# so no link in the destination package tree can point back into the primary checkout or an
# external directory.
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
  find "$destination" -type d -exec chmod u+w {} +
  python3 - "$source" "$destination" <<'PY'
import os
from pathlib import Path
import shutil
import stat
import sys

src_root = Path(sys.argv[1])
dst_root = Path(sys.argv[2]).resolve()


def copy_target(src_target: Path, dst_path: Path) -> None:
    st = src_target.stat()
    if stat.S_ISDIR(st.st_mode):
        shutil.copytree(src_target, dst_path, symlinks=False)
    else:
        shutil.copy2(src_target, dst_path, follow_symlinks=True)


for dirpath, dirnames, filenames in os.walk(dst_root, followlinks=False):
    current = Path(dirpath)
    for name in list(dirnames) + list(filenames):
        candidate = current / name
        if not candidate.is_symlink():
            continue
        raw = os.readlink(candidate)
        raw_path = Path(raw)
        keep_relative = False
        if not raw_path.is_absolute():
            try:
                resolved = (candidate.parent / raw_path).resolve()
                if resolved.is_relative_to(dst_root):
                    keep_relative = True
            except OSError:
                keep_relative = False
        if keep_relative:
            continue
        rel = candidate.relative_to(dst_root)
        src_candidate = src_root / rel
        if not src_candidate.exists():
            print(
                f"Refusing broken escaping package symlink: {src_candidate} -> {raw}",
                file=sys.stderr,
            )
            raise SystemExit(1)
        src_target = src_candidate.resolve()
        candidate.unlink()
        copy_target(src_target, candidate)
        if candidate.is_dir():
            for sub_dir, _, _ in os.walk(candidate, followlinks=False):
                Path(sub_dir).chmod(stat.S_IMODE(Path(sub_dir).stat().st_mode) | 0o700)
PY
)

# resolve_shared_packages_dir <worktree_path>: print the path to the pin-keyed shared packages
# directory, keyed by cslib revision and the full manifest/toolchain/git dependency state, or fail
# if COMPLEXITYLIB_SHARED_PACKAGES_ROOT points into the primary checkout.
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


def git_head(repo: Path) -> str | None:
    if not (repo / ".git").exists():
        return None
    try:
        rev = subprocess.check_output(
            ["git", "-C", str(repo), "rev-parse", "HEAD"],
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
        return rev or None
    except (OSError, subprocess.CalledProcessError):
        return None


def revs_match(a: str, b: str) -> bool:
    n = min(len(a), len(b), 8)
    return n > 0 and a[:n] == b[:n]


manifest = wt_path / "lake-manifest.json"
if not manifest.is_file():
    manifest = root / "lake-manifest.json"

toolchain_file = wt_path / "lean-toolchain"
if not toolchain_file.is_file():
    toolchain_file = root / "lean-toolchain"
toolchain = (
    toolchain_file.read_text(encoding="utf-8").strip()
    if toolchain_file.is_file()
    else None
)

manifest_pkgs: dict[str, str] = {}
if manifest.is_file():
    try:
        data = json.loads(manifest.read_text(encoding="utf-8"))
        for pkg in data.get("packages", []):
            if isinstance(pkg, dict):
                name = pkg.get("name")
                rev = pkg.get("rev")
                if isinstance(name, str) and name and isinstance(rev, str) and rev:
                    manifest_pkgs[name] = rev
    except (OSError, ValueError, TypeError):
        pass

git_heads: dict[str, str] = {}
pkgs_dir = root / ".lake/packages"
if pkgs_dir.is_dir():
    for child in sorted(pkgs_dir.iterdir()):
        if child.is_dir():
            h = git_head(child)
            if h:
                git_heads[child.name] = h

cslib_rev = manifest_pkgs.get("cslib") or git_heads.get("cslib") or ""
cslib_short = cslib_rev[:8] if cslib_rev else None

# Build a full dependency/toolchain state fingerprint whenever anything beyond a single cslib entry
# is present (e.g. mathlib or other package pins, lean-toolchain, or package git checkouts).
other_manifest_pkgs = {k: v for k, v in manifest_pkgs.items() if k != "cslib"}
other_git_heads = {k: v for k, v in git_heads.items() if k != "cslib" and k not in manifest_pkgs}

if cslib_short:
    if not other_manifest_pkgs and not other_git_heads and toolchain is None:
        pin_name = f"packages-cslib-{cslib_short}"
    else:
        merged_pkgs = dict(git_heads)
        merged_pkgs.update(manifest_pkgs)
        state = {"packages": sorted(merged_pkgs.items()), "toolchain": toolchain}
        digest = hashlib.sha256(json.dumps(state, sort_keys=True).encode()).hexdigest()[:8]
        pin_name = f"packages-cslib-{cslib_short}-{digest}"
elif manifest.is_file() or toolchain is not None or git_heads:
    raw = manifest.read_bytes() if manifest.is_file() else b""
    state_bytes = raw + b"\0" + json.dumps({"git": sorted(git_heads.items()), "tc": toolchain}, sort_keys=True).encode()
    digest = hashlib.sha256(state_bytes).hexdigest()[:8]
    pin_name = f"packages-manifest-{digest}"
else:
    pin_name = "packages-cslib-default"


def legacy_dir_matches_manifest(cand: Path) -> bool:
    if not cand.is_dir() or not manifest_pkgs:
        return False
    for name, want_rev in manifest_pkgs.items():
        pkg_dir = cand / name
        if not pkg_dir.is_dir():
            return False
        actual = git_head(pkg_dir)
        if not actual or not revs_match(actual, want_rev):
            return False
    return True


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

shared_roots = []
try:
    wt_parent = wt_path.resolve().parent
    if not in_primary_checkout(wt_parent) and wt_parent != worktrees_root:
        shared_roots.append(wt_parent / ".shared")
except OSError:
    pass
shared_roots.append(worktrees_root / ".shared")
shared_roots.append(Path(f"{root}-wt") / ".shared")

for sroot in shared_roots:
    cand = sroot / pin_name
    if cand.is_dir() and not in_primary_checkout(cand.resolve()):
        print(cand)
        raise SystemExit(0)
    if cslib_short:
        legacy = sroot / f"packages-cslib-{cslib_short}"
        if (
            legacy != cand
            and legacy.is_dir()
            and not in_primary_checkout(legacy.resolve())
            and legacy_dir_matches_manifest(legacy)
        ):
            print(legacy)
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

# root_packages_match_manifest <worktree_path>: return 0 unless the target manifest/toolchain
# disagrees with $ROOT's manifest/toolchain or any package git checkout under $ROOT/.lake/packages.
root_packages_match_manifest() {
  local wt_path="$1"
  python3 - "$ROOT" "$wt_path" <<'PY'
import json
from pathlib import Path
import subprocess
import sys

root = Path(sys.argv[1]).resolve()
wt_path = Path(sys.argv[2])


def revs_match(a: str, b: str) -> bool:
    n = min(len(a), len(b), 8)
    return n > 0 and a[:n] == b[:n]


def load_pkgs(path: Path) -> dict[str, str]:
    if not path.is_file():
        return {}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        out: dict[str, str] = {}
        for pkg in data.get("packages", []):
            if isinstance(pkg, dict):
                name = pkg.get("name")
                rev = pkg.get("rev")
                if isinstance(name, str) and name and isinstance(rev, str) and rev:
                    out[name] = rev
        return out
    except (OSError, ValueError, TypeError):
        return {}


wt_tc = wt_path / "lean-toolchain"
root_tc = root / "lean-toolchain"
if wt_tc.is_file() and root_tc.is_file():
    if wt_tc.read_text(encoding="utf-8").strip() != root_tc.read_text(encoding="utf-8").strip():
        print(
            "Root lean-toolchain does not match worktree lean-toolchain; skipping mismatched package seed.",
            file=sys.stderr,
        )
        raise SystemExit(1)

wt_manifest = wt_path / "lake-manifest.json"
root_manifest = root / "lake-manifest.json"
target_pkgs = load_pkgs(wt_manifest if wt_manifest.is_file() else root_manifest)
root_pkgs = load_pkgs(root_manifest)

for name, want_rev in target_pkgs.items():
    pkg_git = root / ".lake/packages" / name / ".git"
    if pkg_git.exists():
        try:
            actual_rev = subprocess.check_output(
                ["git", "-C", str(pkg_git.parent), "rev-parse", "HEAD"],
                text=True,
                stderr=subprocess.DEVNULL,
            ).strip()
            if actual_rev and not revs_match(actual_rev, want_rev):
                print(
                    f"Root .lake/packages/{name} ({actual_rev[:8]}) does not match manifest pin ({want_rev[:8]}); skipping mismatched package seed.",
                    file=sys.stderr,
                )
                raise SystemExit(1)
        except (OSError, subprocess.CalledProcessError):
            pass
PY
}

# ensure_shared_packages <worktree_path> <shared_pkg_dir>: create <shared_pkg_dir> once as an
# isolated read-only copy of $ROOT/.lake/packages (protecting both files and directories against
# modification or atomic replacement) when not already present; never update in place.
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
    if ! seed_package "$pkg" "$staging/$name" "true"; then
      chmod -R u+w "$staging" 2>/dev/null || true
      rm -rf "$staging"
      return 1
    fi
  done
  chmod -R a-w "$staging"
  if ! python3 - "$staging" "$shared_pkg_dir" <<'PY'
import os
from pathlib import Path
import shutil
import stat
import sys

staging = Path(sys.argv[1])
target = Path(sys.argv[2])


def make_writable_and_remove(path: Path) -> None:
    if not path.exists():
        return
    for dirpath, dirnames, filenames in os.walk(path, followlinks=False):
        p = Path(dirpath)
        p.chmod(stat.S_IMODE(p.stat().st_mode) | 0o700)
        for fname in filenames:
            fp = p / fname
            if not fp.is_symlink():
                fp.chmod(stat.S_IMODE(fp.stat().st_mode) | 0o600)
    shutil.rmtree(path)


if target.exists():
    make_writable_and_remove(staging)
else:
    try:
        os.rename(staging, target)
    except OSError:
        make_writable_and_remove(staging)
        if not target.exists():
            raise
PY
  then
    chmod -R u+w "$staging" 2>/dev/null || true
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
