#!/usr/bin/env bash
# Upload this checkout's and its pinned CSLib library's build outputs to the remote cache.
# Run by `main` CI after a successful build; it needs write access to the bucket.
#
# Usage: scripts/cache/upload.sh <bucket>
#
# Object layout (the one `lake cache put --repo=cslib-community/complexitylib` produces, which
# `lake cache get` reads; artifacts are content-addressed module archives):
#   gs://<bucket>/a0/cslib-community/complexitylib/<hash>.art
#   gs://<bucket>/r0/cslib-community/complexitylib/tc/<toolchain>/<commit>.jsonl
# `lake cache put` re-uploads every artifact on each run; this script uploads only new ones
# (`--no-clobber`) and writes the revision mapping last, so a published mapping never refers to
# a missing artifact. The writer cannot overwrite objects, so published artifacts are immutable.
set -euo pipefail
cd "$(dirname "$0")/../.."

bucket="${1:?Usage: scripts/cache/upload.sh <bucket>}"
scope="cslib-community/complexitylib"
rev="$(git rev-parse HEAD)"
if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  echo "Refusing to upload: the work tree differs from $rev." >&2
  exit 1
fi
cslib_dir=".lake/packages/cslib"
cslib_rev="$(git -C "$cslib_dir" rev-parse HEAD)"
cslib_pin="$(python3 -c 'import json; print(next(p["rev"] for p in json.load(open("lake-manifest.json"))["packages"] if p["name"] == "cslib"))')"
if [ "$cslib_rev" != "$cslib_pin" ] ||
    [ -n "$(git -C "$cslib_dir" status --porcelain --untracked-files=no)" ]; then
  echo "Refusing to upload: CSLib must be clean at the manifest pin $cslib_pin." >&2
  exit 1
fi
# `leanprover/lean4:v4.36.0` → `leanprover--lean4---v4.36.0`, as Lake names toolchain scopes.
toolchain="$(tr -d '[:space:]' < lean-toolchain | sed 's#/#--#; s#:#---#')"

stage="$(mktemp -d "${TMPDIR:-/tmp}/complexitylib-cache.XXXXXX")"
trap 'rm -rf "$stage"' EXIT
# Cover standalone `lake build` too, not only the CSLib modules Complexitylib imports.
# Keep CSLib's own options and natural dependency hashes; no native executables are published.
lake build --wfail --iofail @cslib/Cslib --package=cslib -o "$stage/cslib.jsonl"
lake build Complexity ComplexityTests -o "$stage/complexitylib.jsonl"

publish() {
  local package_scope="$1" package_rev="$2" name="$3" f base count
  lake cache stage "$stage/$name.jsonl" "$stage/$name"
  mkdir "$stage/$name-art"
  for f in "$stage/$name"/*.ltar; do
    base="$(basename "$f" .ltar)"
    mv "$f" "$stage/$name-art/$base.art"
  done
  count="$(find "$stage/$name-art" -name '*.art' | wc -l | tr -d ' ')"
  echo "Uploading up to $count artifacts for $package_scope@$package_rev (existing objects are skipped)"
  find "$stage/$name-art" -name '*.art' | gcloud storage cp --no-clobber --quiet \
    --content-type=application/vnd.reservoir.artifact -I "gs://$bucket/a0/$package_scope/"
  gcloud storage cp --no-clobber --quiet \
    --content-type=application/vnd.reservoir.outputs+json-lines \
    "$stage/$name.jsonl" "gs://$bucket/r0/$package_scope/tc/$toolchain/$package_rev.jsonl"
  echo "Published gs://$bucket/r0/$package_scope/tc/$toolchain/$package_rev.jsonl"
}

publish leanprover/cslib "$cslib_rev" cslib
publish "$scope" "$rev" complexitylib
