#!/usr/bin/env bash
# Start the Brigade server. All knobs are env vars; see .env.example.
set -euo pipefail
cd "$(dirname "$0")/../server"
if [ -f ../.env ]; then set -a; . ../.env; set +a; fi
exec python -m uvicorn app.main:app --host "${HOST:-0.0.0.0}" --port "${PORT:-8811}"
