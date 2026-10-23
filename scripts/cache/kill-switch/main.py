"""Stop public downloads from the remote cache when spending or egress crosses its limit.

Deployed as a Pub/Sub-triggered Cloud Run function by scripts/cache/setup-gcs.sh. It receives
two kinds of message on the same topic:

* Cloud Billing budget notifications (`costAmount`, `budgetAmount`): acts once the cost reaches
  the budget;
* Cloud Monitoring alert notifications (`incident.state`): acts when the egress alert opens.

Acting means removing `allUsers` from the bucket's IAM policy. Objects are kept, so the
maintainer restores service by re-granting public read (see scripts/cache/README.md).
"""

import base64
import json
import os

import functions_framework
from google.cloud import storage

BUCKET = os.environ["BUCKET"]


def should_stop(message: dict) -> bool:
    if "costAmount" in message and "budgetAmount" in message:
        return float(message["costAmount"]) >= float(message["budgetAmount"])
    return message.get("incident", {}).get("state") == "open"


@functions_framework.cloud_event
def handle(cloud_event) -> None:
    message = json.loads(base64.b64decode(cloud_event.data["message"]["data"]))
    if not should_stop(message):
        return
    bucket = storage.Client().bucket(BUCKET)
    policy = bucket.get_iam_policy(requested_policy_version=3)
    changed = False
    for binding in policy.bindings:
        if "allUsers" in binding["members"]:
            binding["members"].discard("allUsers")
            changed = True
    policy.bindings = [b for b in policy.bindings if b["members"]]
    if changed:
        bucket.set_iam_policy(policy)
        print(f"Removed public read from gs://{BUCKET}: {json.dumps(message)[:500]}")
