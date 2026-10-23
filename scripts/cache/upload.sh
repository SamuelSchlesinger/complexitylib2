#!/usr/bin/env bash
# Upload this checkout's build outputs to the remote cache. Run by `main` CI after a successful
# build; it needs write access to the bucket and is not meant for local use.
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
# `leanprover/lean4:v4.36.0` → `leanprover--lean4---v4.36.0`, as Lake names toolchain scopes.
toolchain="$(tr -d '[:space:]' < lean-toolchain | sed 's#/#--#; s#:#---#')"

stage="$(mktemp -d "${TMPDIR:-/tmp}/complexitylib-cache.XXXXXX")"
trap 'rm -rf "$stage"' EXIT
lake build Complexity ComplexityTests -o "$stage/mappings.jsonl"
lake cache stage "$stage/mappings.jsonl" "$stage/out"
mkdir "$stage/art"
for f in "$stage"/out/*.ltar; do
  base="$(basename "$f" .ltar)"
  mv "$f" "$stage/art/$base.art"
done
count="$(find "$stage/art" -name '*.art' | wc -l | tr -d ' ')"
echo "Uploading up to $count artifacts for $rev (existing objects are skipped)"
find "$stage/art" -name '*.art' | gcloud storage cp --no-clobber --quiet \
  --content-type=application/vnd.reservoir.artifact -I "gs://$bucket/a0/$scope/"
gcloud storage cp --no-clobber --quiet \
  --content-type=application/vnd.reservoir.outputs+json-lines \
  "$stage/mappings.jsonl" "gs://$bucket/r0/$scope/tc/$toolchain/$rev.jsonl"
echo "Published gs://$bucket/r0/$scope/tc/$toolchain/$rev.jsonl"
