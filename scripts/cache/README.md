# Build caches

Complexitylib's build has two caches. Both are optional: `lake build` without them compiles
everything it needs.

**Local artifact cache.** `lakefile.toml` enables Lake's content-addressed artifact cache, so a
module built in one checkout (a worktree, an agent sandbox, a second clone) is reused by every
other checkout on the same machine with the same inputs. Outputs are hard-linked back into
`.lake/build`. `lake cache clean` empties it; it lives in the Lean toolchain's directory under
`~/.elan` unless `LAKE_CACHE_DIR` says otherwise.

**Remote cache.** CI uploads the build outputs of every commit on `main`, together with its
pinned CSLib library. `scripts/cache/get.sh` downloads each package's outputs for its nearest
cached ancestor:

```bash
scripts/build.sh --wfail --iofail   # restore caches, then build changed or missing modules
```

A complete set of Complexitylib library and test outputs is about 70 MB compressed.
Complexitylib sets `platformIndependent = true`, so Linux CI builds serve macOS checkouts.
`COMPLEXITYLIB_CACHE_URL` overrides the location; set it to an empty string to skip the
CSLib and Complexitylib downloads.

## Automatic restoration

`scripts/build.sh` runs `scripts/cache/ensure.sh`, then forwards its arguments and exit status to
`lake build`. `scripts/check.sh` uses the same bootstrap before full or quick validation; a quick
check that falls back to all six gates does not download twice. Bare `lake` commands do not
bootstrap. Before using Lean MCP diagnostics or another operation that can elaborate/build, run:

```bash
scripts/cache/ensure.sh
```

The instruction in `AGENTS.md` applies to every agent client. MCP's
`lean_build(fetch_cache=true)` only fetches Mathlib's cache, so it does not replace this command.

The bootstrap records a completed **attempt**, not a successful cache hit, in
`.lake/cache-bootstrap/attempt.json`. For ten minutes it skips another attempt with the same
checkout path, `HEAD`, toolchain, manifest, Lake configuration, endpoint and `LAKE_CACHE_DIR`.
Working proof edits do not trigger another download. A changed `HEAD`, pin or configuration
triggers a new attempt; an unchanged state is retried after ten minutes, including a previous miss or
network failure. The stamp is written atomically after the fetch command finishes.

```bash
scripts/cache/ensure.sh --refresh             # retry now, e.g. after clearing caches
COMPLEXITYLIB_CACHE_AUTO=0 scripts/build.sh    # skip automatic downloads deliberately
```

The opt-out also applies to `scripts/check.sh` and direct bootstrap calls. It leaves existing
build outputs and Lake's local cache in place. `scripts/cache/get.sh` remains the explicit,
unstamped fetch command. Cache misses and download failures are optional: builds compile what
is missing, and the bootstrap never claims that all requested artifacts were available.

## Standalone CSLib checkouts

From a CSLib checkout using the same Lean toolchain, run:

```bash
lake exe cache get
/path/to/complexitylib/scripts/cache/get-cslib.sh
lake build
```

The helper runs in the caller's directory and downloads the full `Cslib` library, including
modules Complexitylib does not import. It uses CSLib's own Git revision, not Complexitylib's.
Only CSLib revisions pinned by published Complexitylib `main` builds are available; this is not
an upstream CSLib cache service. Lake searches up to 100 commits back, and rebuilds changed or
missing modules normally. No CSLib configuration change is needed to consume the cache.

The cache covers Lean module artifacts, not `CslibTests` or native validation executables.
CSLib's build options and dependency hashes are preserved. The helper selects the platform-free
mapping with `--platform=`; it does not change CSLib's platform settings. Native dependencies or
different compiler options can still prevent reuse. `COMPLEXITYLIB_CACHE_URL` selects the same
bucket as for Complexitylib; an empty value disables the download.

## Trust and privacy

Downloaded `.olean` files are trusted by Lean: imported modules are not re-checked by the
kernel, and their compiled code (tactics, macros, initializers) runs during your build. Whoever
can write to the cache could therefore make a false theorem appear proved or run code on your
machine. The cache is set up so that this is no more trust than building `main` already
requires:

- Only the `main` push job of this repository can write. It authenticates with GitHub's OIDC
  token through Workload Identity Federation, restricted to this repository's numeric id, the
  `main` ref and the `push` event; no credentials are stored in GitHub. Pull requests, forks and
  other workflows cannot obtain write access.
- The writer can create objects but not delete them, so a published artifact can never be
  replaced. Lake checks every downloaded artifact against the hash recorded in the mapping.
- Merge-gating CI always builds from source; the cache only saves local build time.

The cache contains only build outputs of commits on `main` and their pinned public CSLib
sources; build logs and machine paths are not uploaded. Downloads are anonymous HTTPS
requests to Google Cloud Storage; the bucket keeps no access logs.

## Maintainer runbook

The cache runs in a dedicated Google Cloud project maintained by Samuel Schlesinger.

**Setup.** `PROJECT=<id> BILLING_ACCOUNT=<id> ALERT_EMAIL=<address> scripts/cache/setup-gcs.sh`
creates, in order (each step can be rerun alone, e.g. `setup-gcs.sh alert`):

| Step | Creates |
| --- | --- |
| `project` | the project, billing link and APIs |
| `bucket` | `gs://complexitylib-lake-cache` (`us-east1`), public read by object name without listing, no soft delete or versioning, revision mappings expire after 180 days |
| `writer` | the GitHub identity pool and provider, and the `lake-cache-writer` service account (create + read on the bucket only) |
| `budget` | a monthly budget (default 10 USD) with alerts at 50/90/100 % and a Pub/Sub topic |
| `killswitch` | a Cloud Run function that removes public read when the budget is reached or the egress alert fires |
| `alert` | an alert on more than 20 GB sent per hour, to the kill switch and `ALERT_EMAIL` |
| `variables` | prints the `gh variable set` commands for the three repository variables |

CI skips the upload until the repository variable `LAKE_CACHE_BUCKET` is set.

**Costs.** Storage and egress are small at this size: each `main` push uploads only modules whose
outputs changed, and Cloud Storage's free tier covers 5 GB of storage and 100 GB of egress per
month in `us-east1`. The budget alerts and the kill switch bound abuse of the public bucket.

**After the kill switch fires.** Downloads fail and builds fall back to compiling. Check the egress
graph and the function's log, then restore public read:

```bash
gcloud storage buckets add-iam-policy-binding gs://complexitylib-lake-cache \
  --member=allUsers --role=roles/storage.legacyObjectReader
```

**Pruning.** Artifacts are shared between revisions, so they are not expired by age. When storage
grows, delete the artifacts that no revision mapping still in the bucket refers to.

**Layout.** `a0/cslib-community/complexitylib/<hash>.art` holds module archives and
`r0/cslib-community/complexitylib/tc/<toolchain>/<commit>.jsonl` the input-to-output mappings of
each commit, as written by `scripts/cache/upload.sh` and read by `lake cache get`.
CSLib uses `a0/leanprover/cslib/<hash>.art` and
`r0/leanprover/cslib/tc/<toolchain>/<cslib-commit>.jsonl` in the same bucket. The publisher checks
that the CSLib checkout is clean at the manifest pin, builds the full library with strict
warnings/errors, and uploads its archives before its mapping. The first publication of a pin
can build CSLib modules not needed by Complexitylib. Only new archives are uploaded thereafter.
