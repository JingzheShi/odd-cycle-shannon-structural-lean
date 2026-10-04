#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
: "${WANDB_ENTITY:?Set WANDB_ENTITY to your W&B entity and authenticate first}"
task="${1:-proofs}"
case "$task" in
  proofs)
    python3 scripts/run_logged.py --name structural-clean-proof-build \
      --receipt logs/proofs.json --timeout 14400 -- \
      bash -c 'cd lean && lake exe cache get && lake build StructuralRelease'
    ;;
  paper)
    python3 scripts/run_logged.py --name structural-paper-build \
      --receipt logs/paper.json --timeout 180 -- bash scripts/build_paper.sh
    ;;
  *) printf 'Usage: %s [proofs|paper]\n' "$0" >&2; exit 2 ;;
esac
