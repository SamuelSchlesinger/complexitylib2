#!/usr/bin/env bash
# Manage isolated git worktrees under .worktrees/ with pre-seeded .lake caches.
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
# Cache seeding note:
#   By default, `.lake/packages` is hard-linked (`cp -al`) from the root checkout for speed
#   and disk efficiency, while `.lake/build` and `.lake/config` are copied (`cp -r`) so build
#   outputs remain isolated. Because hard-linked files share inodes with the root checkout, do
#   not mutate files inside `.lake/packages/` in a default worktree. `--copy-cslib` copies only
#   `.lake/packages/cslib` (for upstream cslib edits or a cslib pin bump) and still hard-links
#   every other package, including mathlib; `--copy-packages` copies all packages (several GB),
#   for example when the Mathlib pin changes.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
GIT_COMMON_DIR="$(git -C "$SCRIPT_DIR" rev-parse --path-format=absolute --git-common-dir)"
ROOT="$(cd "$GIT_COMMON_DIR/.." && pwd)"
cd "$ROOT"

# seed_lake <worktree_path> <copy_mode>, where copy_mode is `none`, `cslib` or `all`.
seed_lake() {
  local wt_path="$1"
  local copy_mode="${2:-none}"
  if [ ! -d "$ROOT/.lake" ]; then
    echo "No root .lake directory found at $ROOT/.lake; skipping cache seed."
    return 0
  fi
  mkdir -p "$wt_path/.lake"
  if [ -d "$ROOT/.lake/packages" ] && [ ! -d "$wt_path/.lake/packages" ]; then
    case "$copy_mode" in
      all)
        cp -r "$ROOT/.lake/packages" "$wt_path/.lake/packages"
        ;;
      cslib)
        mkdir -p "$wt_path/.lake/packages"
        for pkg in "$ROOT"/.lake/packages/*; do
          local name
          name="$(basename "$pkg")"
          if [ "$name" = "cslib" ]; then
            cp -r "$pkg" "$wt_path/.lake/packages/cslib"
          else
            cp -al "$pkg" "$wt_path/.lake/packages/$name"
          fi
        done
        ;;
      *)
        cp -al "$ROOT/.lake/packages" "$wt_path/.lake/packages"
        ;;
    esac
  fi
  if [ -d "$ROOT/.lake/config" ] && [ ! -d "$wt_path/.lake/config" ]; then
    cp -r "$ROOT/.lake/config" "$wt_path/.lake/config"
  fi
  if [ -d "$ROOT/.lake/build" ] && [ ! -d "$wt_path/.lake/build" ]; then
    cp -r "$ROOT/.lake/build" "$wt_path/.lake/build"
  fi
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
    for wt in "$ROOT"/.worktrees/*; do
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
        rm -rf "$wt/.lake"
        git worktree remove --force "$wt"
      fi
    done
    ;;
  *)
    echo "Unknown command: $cmd" >&2
    exit 1
    ;;
esac
