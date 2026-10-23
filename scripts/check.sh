#!/usr/bin/env bash
# Run the validation sequence of AGENTS.md (cslib's CI) and report each gate.
# Usage: scripts/check.sh [--quick [--base REF]] (from the repository root or any worktree)
set -u
cd "$(dirname "$0")/.." || exit 1
if (($#)); then
  if [ "$1" = "--quick" ]; then
    shift
    exec python3 scripts/quick_check.py "$@"
  fi
  echo "Usage: scripts/check.sh [--quick [--base REF]]" >&2
  exit 2
fi
log_dir=$(mktemp -d "${TMPDIR:-/tmp}/complexitylib-check.XXXXXX") || exit 1
status=0
gate=0
run() {
  local name=$1
  shift
  gate=$((gate + 1))
  local log="$log_dir/$gate.log"
  if "$@" >"$log" 2>&1; then
    printf 'ok    %s\n' "$name"
  else
    printf 'FAIL  %s\n' "$name"
    cat "$log"
    status=1
  fi
}
run "build --wfail --iofail" lake build --wfail --iofail
run "mk_all --check" lake exe mk_all --check
run "test --wfail --iofail" lake test --wfail --iofail
run "lint" lake lint
run "lint-style" lake exe lint-style
run "checkInitImports" lake exe checkInitImports
if ((status)); then
  printf 'Full logs: %s\n' "$log_dir"
else
  rm "$log_dir"/*.log
  rmdir "$log_dir"
fi
exit $status
