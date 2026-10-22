#!/usr/bin/env bash
# Manage isolated git worktrees under .worktrees/ with pre-seeded .lake caches.
#
# Usage:
#   scripts/worktree.sh create <branch> [dir_name] [base_ref] [--copy-cslib] [--force-reset]
#   scripts/worktree.sh seed <worktree_path> [--copy-cslib]
#   scripts/worktree.sh list
#   scripts/worktree.sh prune-merged [base_ref] [--dry-run]
#
# Cache seeding note:
#   By default, `.lake/packages` is hard-linked (`cp -al`) from the root checkout for speed
#   and disk efficiency, while `.lake/build` and `.lake/config` are copied (`cp -r`) so build
#   outputs remain isolated. Because hard-linked files share inodes with the root checkout, do
#   not mutate files inside `.lake/packages/` in a default worktree; pass `--copy-cslib` when
#   testing upstream cslib edits or syncing the cslib pin.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
GIT_COMMON_DIR="$(git -C "$SCRIPT_DIR" rev-parse --path-format=absolute --git-common-dir)"
ROOT="$(cd "$GIT_COMMON_DIR/.." && pwd)"
cd "$ROOT"

seed_lake() {
  local wt_path="$1"
  local copy_cslib="${2:-false}"
  if [ ! -d "$ROOT/.lake" ]; then
    echo "No root .lake directory found at $ROOT/.lake; skipping cache seed."
    return 0
  fi
  mkdir -p "$wt_path/.lake"
  if [ -d "$ROOT/.lake/packages" ] && [ ! -d "$wt_path/.lake/packages" ]; then
    if [ "$copy_cslib" = "true" ]; then
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
    else
      cp -al "$ROOT/.lake/packages" "$wt_path/.lake/packages"
    fi
  fi
  if [ -d "$ROOT/.lake/config" ] && [ ! -d "$wt_path/.lake/config" ]; then
    cp -r "$ROOT/.lake/config" "$wt_path/.lake/config"
  fi
  if [ -d "$ROOT/.lake/build" ] && [ ! -d "$wt_path/.lake/build" ]; then
    cp -r "$ROOT/.lake/build" "$wt_path/.lake/build"
  fi
}

cmd="${1:-list}"
shift || true

case "$cmd" in
  create)
    branch="${1:?Usage: scripts/worktree.sh create <branch> [dir_name] [base_ref] [--copy-cslib] [--force-reset]}"
    shift
    dir_name=""
    base_ref=""
    copy_cslib="false"
    force_reset="false"
    for arg in "$@"; do
      if [ "$arg" = "--copy-cslib" ]; then
        copy_cslib="true"
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
        seed_lake "$wt_path" "$copy_cslib"
        echo "Ready: $wt_path (branch $branch reset to $effective_base)"
      else
        if [ -n "$base_ref" ]; then
          echo "Branch '$branch' already exists locally; refusing to reset it to '$base_ref' without --force-reset." >&2
          exit 1
        fi
        git worktree add "$wt_path" "$branch"
        seed_lake "$wt_path" "$copy_cslib"
        echo "Ready: $wt_path (existing branch $branch)"
      fi
    else
      effective_base="${base_ref:-origin/main}"
      git worktree add -b "$branch" "$wt_path" "$effective_base"
      seed_lake "$wt_path" "$copy_cslib"
      echo "Ready: $wt_path (new branch $branch from $effective_base)"
    fi
    ;;
  seed)
    wt_path="${1:?Usage: scripts/worktree.sh seed <worktree_path> [--copy-cslib]}"
    copy_cslib="false"
    if [ "${2:-}" = "--copy-cslib" ]; then
      copy_cslib="true"
    fi
    seed_lake "$wt_path" "$copy_cslib"
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
