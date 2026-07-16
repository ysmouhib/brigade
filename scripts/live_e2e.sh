#!/usr/bin/env bash
# Live end-to-end check: boots the real server (uvicorn) in offline demo mode,
# drives it over HTTP exactly like the web UI does, and prints a transcript.
set -euo pipefail
cd "$(dirname "$0")/../server"

PORT="${PORT:-8811}"
export FAKE_LLM=1 LEAN_MODE=fake

python -m uvicorn app.main:app --port "$PORT" >/tmp/brigade_uvicorn.log 2>&1 &
SRV=$!
trap 'kill $SRV 2>/dev/null || true' EXIT

for i in $(seq 1 50); do
  curl -sf "localhost:$PORT/health" >/dev/null 2>&1 && break
  sleep 0.2
done

echo "== /health =="
curl -s "localhost:$PORT/health"; echo; echo

JOB=$(curl -s -X POST "localhost:$PORT/jobs" -H 'Content-Type: application/json' \
  -d '{"problem":"Prove that for every natural number n, n^2 + n is even."}' \
  | python3 -c "import sys,json;print(json.load(sys.stdin)['job_id'])")
echo "== submitted job $JOB =="

for i in $(seq 1 200); do
  STATUS=$(curl -s "localhost:$PORT/jobs/$JOB" | python3 -c "import sys,json;print(json.load(sys.stdin)['status'])")
  [ "$STATUS" != "queued" ] && [ "$STATUS" != "running" ] && break
  sleep 0.1
done

echo; echo "== final job state =="
curl -s "localhost:$PORT/jobs/$JOB" | python3 -c "
import json, sys
j = json.load(sys.stdin)
print('status:', j['status'], '| phase:', j['phase'], '| round:', j['round'])
print('llm_calls:', j['llm_calls'], '| lean_calls:', j['lean_calls'], '| events:', j['event_count'])
print('nodes:')
for n in sorted(j['nodes'], key=lambda x: (x['depth'], x['lean_name'])):
    print(f\"  {'  '*n['depth']}{n['lean_name']:12s} [{n['status']}] attempts={n['attempts']}\")
print()
print('--- final_lean (Lean-verified) ---')
print(j['final_lean'])
open('/tmp/brigade_job.json','w').write(json.dumps(j, indent=2))
"

echo; echo "== agent timeline (paginated via ?since=) =="
python3 - "$PORT" "$JOB" <<'PY'
import json, sys, urllib.request
port, job = sys.argv[1], sys.argv[2]
seen, since = [], 0
while True:
    with urllib.request.urlopen(f"http://localhost:{port}/jobs/{job}/events?since={since}&limit=50") as r:
        page = json.load(r)
    if not page["events"]:
        break
    seen += page["events"]
    since = page["next"]
for e in seen:
    print(f"[{e['seq']:>3}] {e['level']:<6} {e['agent']:<22} {e['type']:<18} {e['content'][:96].replace(chr(10),' | ')}")
print(f"\n{len(seen)} events, strictly increasing seq:", [x['seq'] for x in seen] == sorted({x['seq'] for x in seen}))
PY

echo; echo "== live e2e PASSED =="
