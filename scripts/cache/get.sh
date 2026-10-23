#!/usr/bin/env bash
# Download prebuilt build outputs, so that `lake build` only compiles what you changed.
#
# Usage: scripts/cache/get.sh            (from the repository root or any worktree)
#
# Fetches Mathlib's cache, the pinned CSLib library, then Complexitylib's outputs for the nearest
# ancestor that `main` CI has uploaded (Lake looks back up to 100 commits). Missing outputs are not an error:
# `lake build` compiles whatever the cache did not provide. See scripts/cache/README.md.
set -u
cd "$(dirname "$0")/../.." || exit 1

url="${COMPLEXITYLIB_CACHE_URL-https://storage.googleapis.com/complexitylib-lake-cache}"

lake exe cache get || echo "warning: Mathlib cache download failed; lake build will compile Mathlib" >&2
if [ -z "$url" ]; then
  echo "COMPLEXITYLIB_CACHE_URL is empty; skipping the Complexitylib cache." >&2
  exit 0
fi
scripts/cache/get-cslib.sh --package=cslib
if ! LAKE_CACHE_ARTIFACT_ENDPOINT="$url/a0" LAKE_CACHE_REVISION_ENDPOINT="$url/r0" \
    lake cache get --repo=cslib-community/complexitylib; then
  echo "note: no cached Complexitylib outputs found for this history; lake build will compile them" >&2
fi
