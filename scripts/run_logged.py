import argparse
import json
import os
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path

import wandb

parser = argparse.ArgumentParser(description="Log a reproduction command to W&B.")
parser.add_argument("--name", required=True)
parser.add_argument("--receipt", required=True)
parser.add_argument("--timeout", type=int, default=3600)
parser.add_argument("command", nargs=argparse.REMAINDER)
arguments = parser.parse_args()
command = arguments.command
if command and command[0] == "--":
    command = command[1:]
if not command:
    parser.error("a command is required after --")
run = wandb.init(project="seven-ring-shannon", entity=os.environ["WANDB_ENTITY"],
    name=arguments.name, job_type="publication-reproduction",
    config={"command": command}, settings=wandb.Settings(init_timeout=30))
started = time.monotonic()
receipt = Path(arguments.receipt)
receipt.parent.mkdir(parents=True, exist_ok=True)
output_path = receipt.with_suffix(".txt")
try:
    with output_path.open("w") as output:
        result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT,
            timeout=arguments.timeout, check=False)
    returncode = result.returncode
except subprocess.TimeoutExpired:
    returncode = 124
record = {"command": command, "returncode": returncode,
    "seconds": time.monotonic() - started, "wandb_run": run.id,
    "wandb_url": run.url, "timestamp": datetime.now(timezone.utc).isoformat(),
    "output": str(output_path)}
receipt.write_text(json.dumps(record, indent=2) + "\n")
run.log({"returncode": returncode, "seconds": record["seconds"]})
run.finish(exit_code=int(returncode != 0))
print(json.dumps(record, indent=2))
raise SystemExit(returncode)
