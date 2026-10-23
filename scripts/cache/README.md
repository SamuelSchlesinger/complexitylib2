# Build caches

Complexitylib's build has two caches. Both are optional: `lake build` without them compiles
everything it needs.

**Local artifact cache.** `lakefile.toml` enables Lake's content-addressed artifact cache, so a
module built in one checkout (a worktree, an agent sandbox, a second clone) is reused by every
other checkout on the same machine with the same inputs. Outputs are hard-linked back into
`.lake/build`. `lake cache clean` empties it; it lives in the Lean toolchain's directory under
`~/.elan` unless `LAKE_CACHE_DIR` says otherwise.

**Remote cache.** CI uploads the build outputs of every commit on `main`; `scripts/cache/get.sh`
downloads them for the nearest cached ancestor of your `HEAD`:

```bash
scripts/cache/get.sh   # Mathlib's cache, then Complexitylib's outputs
lake build             # compiles only what you changed
```

A complete set of library and test outputs is about 70 MB compressed. Outputs are platform
independent (`platformIndependent = true`), so Linux CI builds serve macOS checkouts.
`COMPLEXITYLIB_CACHE_URL` overrides the location; set it to an empty string to skip the
Complexitylib download.

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

The cache contains only build outputs of commits on `main` (sources that are public in this
repository); build logs and machine paths are not uploaded. Downloads are anonymous HTTPS
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
