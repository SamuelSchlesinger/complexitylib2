#!/usr/bin/env bash
# Restore the CSLib library from Complexitylib's cache, using the caller's current directory.
# Usage in a standalone CSLib checkout: /path/to/complexitylib/scripts/cache/get-cslib.sh
# Usage in Complexitylib: scripts/cache/get-cslib.sh --package=cslib
# Fetch Mathlib's cache first (`lake exe cache get`). A miss leaves Lake to compile from source.
set -u
if [ "$#" -gt 1 ] || { [ "$#" -eq 1 ] && [ "$1" != "--package=cslib" ]; }; then
  echo "Usage: $0 [--package=cslib]" >&2
  exit 2
fi
url="${COMPLEXITYLIB_CACHE_URL-https://storage.googleapis.com/complexitylib-lake-cache}"
if [ -z "$url" ]; then
  echo "COMPLEXITYLIB_CACHE_URL is empty; skipping the CSLib cache." >&2
  exit 0
fi
# The empty platform selects the portable module archives. Lake still checks CSLib's actual
# input hashes, including any native dependency; this does not override its build options.
if ! LAKE_CACHE_ARTIFACT_ENDPOINT="$url/a0" LAKE_CACHE_REVISION_ENDPOINT="$url/r0" \
    lake cache get --repo=leanprover/cslib --platform= "$@"; then
  echo "note: no complete CSLib cache found for this history; lake build will compile missing outputs" >&2
fi
