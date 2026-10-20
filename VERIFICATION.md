# VERIFICATION.md — what is verified, where, and how

Rigor demands saying precisely which claims are machine-checked by the test suite
and which require a real Lean toolchain (and an API key) on your machine. Nothing
in the first list is aspirational — every claim is asserted by code that runs in CI
on every push.

## Verified by the test suite (`cd server && python -m pytest -q` → all pass)

Coverage by file:

- `tests/test_numeric.py` — the Skeptic's sympy falsifier: a true identity
  (n²+n even) survives 30 probes; the false claim "every prime is odd" is refuted at
  n=2; injection attempts (`__import__`, attribute access, non-whitelisted names)
  raise `ProbeError` instead of evaluating.
- `tests/test_verifier.py` — the lint catches every forbidden token
  (`sorry, admit, axiom , native_decide, sorryAx, unsafe , @[implemented_by`) and
  does not fire on honest identifiers; Lean output regexes parse real
  error/warning/axiom lines; FakeLean's semantics (rules, bad tokens, sorry
  counting, dirty axiom audit) behave as specified.
- `tests/test_orchestrator.py` — end-to-end on the deterministic demo scenario,
  asserting the mechanisms AND the invariants:
  - job ends PROVED; final file contains all 5 theorems and no `sorry`;
  - all four hierarchy levels (chef/sous/worker/lean) and all seven agent roles
    appear in the event log; 3 brainstormers ran;
  - the statement gate caught the intentionally broken `Evenn` formalization and
    forced a retry (statement gate);
  - lemma_1 needed ≥2 attempts with a Critic triage in between (repair cycle);
  - lemma_2 was decomposed into lemma_2_a/lemma_2_b, both verified, and its final
    proof cites both (escalation);
  - **I1**: every `verified` event is preceded by a Lean OK check on that node —
    checked event-by-event over the whole log;
  - **I2**: the `proved` event comes only after a whole-file re-check and an axiom
    audit whose event shows `ok=True` without `sorryAx`; the exact `final_lean`
    string was seen verbatim by the verifier;
  - **I3**: a prover echoing a different, trivially provable theorem line gets
    stripped; the pinned statement is what reaches Lean;
  - **I4**: a prover answering `sorry` is rejected by lint, the job ends EXHAUSTED
    (never PROVED), and Lean saw `sorry` only from the intentional statement gate —
    proven by counting the verifier's actual inputs;
  - the Skeptic refutation path: on "every prime is odd" the job ends REFUTED with
    counterexample `{n: 2}`, and the script *asserts no prover or strategist is ever
    consulted* (their handler raises).
- `tests/test_strategic.py` — `VERIFY_POLICY=strategic` is faster without being
  weaker:
  - **Batching is real and sound**: with two provable sibling lemmas, exactly ONE
    Lean call contains both proofs and none contains just one; soundness is
    re-asserted directly — every VERIFIED node's exact pinned theorem text appears
    verbatim in an error-free, sorry-free verifier input.
  - **Batch failure degrades gracefully**: one bad sibling makes the combined check
    fail, a `batch_split` event fires, the good sibling verifies individually, and
    the bad one enters the normal repair cycle and succeeds on attempt 2.
  - **Per-lemma refutation**: a planned lemma "every prime is odd" is killed by
    sympy at n=2 *before any prover call* (the scripted prover raises if consulted),
    the node ends REFUTED and survives round abandonment, and the failure feedback
    reaches the chef.
- `tests/test_v2.py` — the proving-power features, each shown to leave acceptance
  untouched:
  - **tactic cascade**: a lemma the automation closes is VERIFIED with zero prover
    calls (the scripted prover raises if consulted), the cascade body itself was
    seen and OK'd by the verifier (I1), and a failing cascade falls through to the
    normal prover loop;
  - **sampled first attempts**: with `PROVE_SAMPLES=3`, three parallel candidates
    are generated, only the Lean-passing one is accepted, attempts are counted, and
    an all-fail sample feeds its errors into the ordinary repair cycle;
  - **REPL efficiency and goals**: with a stubbed REPL, a verified-helper context is
    elaborated exactly once and reused via its environment id across checks, and the
    goal state of a `by sorry` statement check is extracted;
  - **premise retrieval** parses loogle-shaped hits and returns [] on any HTTP
    failure or unknown backend (never blocking the pipeline);
  - **prover routing** sends role=prover to the dedicated model and every other
    role to the primary;
  - **SQLite persistence**: a finished job written by one Store is loaded intact by
    a fresh Store on the same path.
- `tests/test_api.py` — over the real ASGI app: submit → poll to `proved` exactly
  like the web UI; `/events?since=` cursor pagination returns every event exactly
  once in order; job listing; cancel-after-completion is a no-op; 404 and
  empty-problem 422; **cancelling a genuinely running job** (hanging LLM) flips it
  to `cancelled`; bearer auth returns 401 without the token, 200 with it, and
  `/health` stays open; oversized budget overrides are clamped. Key/setup flow:
  with no key, `GET /` serves the UI, `POST /jobs` on the claude engine returns a
  clear 409 (never a silent fallback), the demo engine runs to `proved` and is
  labeled `engine=demo`, and `POST /settings` flips `has_key` without touching disk
  unless `remember` is set. **Replay-engine honesty guard**: `POST /jobs` with the
  replay engine and any problem other than the fixed recorded scenario returns 409
  with an explanation, and the served UI page carries the honest labeling.

### Contract tests (added in Phase 0)

The tests above all run on fakes, which is how three real-mode failures went
unnoticed. These tests pin the boundaries to real formats:

- `tests/test_llm_contract.py` — the installed `anthropic` SDK itself, over a
  mocked transport: no unsupported sampling parameters are sent, roles route to
  the right model, a 400 stops the job without retries, overload is retried.
- `tests/test_config.py` — `.env` values with inline comments and quotes parse;
  unknown `LEAN_MODE`/`VERIFY_POLICY`/`RETRIEVAL` values and bad integers fail
  loudly; real Claude jobs refuse the fake verifier; `.env.example` has no inline
  comments; `scripts/load_env.ps1` is exercised wherever PowerShell exists.
- `tests/test_repl_contract.py` — the Lean REPL's JSON format (a reply recorded
  in the REPL's own test suite at v4.15.0, plus its `info` severity): sorry
  warnings count, `#print axioms` is read, the audit fails closed.
- `tests/test_skeptic_safety.py` — oversized candidates are skipped, a runaway
  probe times out in its worker process while the event loop keeps running,
  numeric refutations are labeled as not Lean-checked.
- `tests/test_lean_fixtures.py` — replays real `lake env lean` and REPL outputs
  from `tests/fixtures/lean/`. Skipped until you record them (step A below).

## Verified over real HTTP (`scripts/live_e2e.sh`)

Boots uvicorn (`FAKE_LLM=1 LEAN_MODE=fake`), submits the demo problem with curl,
polls, and prints the timeline (a captured transcript is in
`VERIFICATION_transcript.txt`). Result: `status: proved`, 15 Lean calls, 53 events
with strictly increasing seq. The five verified nodes:

```
thm_main   [verified] attempts=1
  lemma_1    [verified] attempts=2     ← repair cycle visible in the timeline
  lemma_2    [verified] attempts=3     ← decomposition escalation
    lemma_2_a  [verified] attempts=1
    lemma_2_b  [verified] attempts=1
```

Note what the fake preserves: FakeLean is rule-driven (a block "compiles" only if it
contains required tokens), so even in demo mode the LLM script cannot mark anything
proved — the acceptance path is identical to production, only the two external
processes (the Anthropic API, the `lean` binary) are substituted.

## To verify on your machine (exact commands)

**A. Real Lean verifier** (once, ~5-10 GB):

```bash
bash scripts/setup_lean.sh
```

The script ends by running the exact code path the server uses (`lake env lean` on a
scratch file) against this theorem, including an axiom print:

```lean
theorem brigade_smoke (n : ℕ) : Even (n ^ 2 + n) := by
  have h : n ^ 2 + n = n * (n + 1) := by ring
  rw [h]
  exact Nat.even_mul_succ_self n
```

Then record the contract fixtures from your real toolchain and run the suite:

```bash
python3 scripts/record_lean_fixtures.py
cd server && python -m pytest -q tests/test_lean_fixtures.py
```

Commit `server/tests/fixtures/lean/`; re-record after every Lean upgrade.

If it prints the axiom line and exits 0, the verifier backend is good.

**B. Real end-to-end with Claude:**

```bash
cp .env.example .env    # add ANTHROPIC_API_KEY
bash scripts/run_server.sh
curl -X POST localhost:8811/jobs -H 'Content-Type: application/json' \
  -d '{"problem":"Prove that for every natural number n, n^2 + n is even."}'
```

Golden-path expectations: status `proved`; `final_lean` compiles standalone in the
BrigadeLean project; the axiom_audit event lists only propext / Classical.choice /
Quot.sound. Then try the refutation path with
`"Prove that every prime number is odd."` and expect `refuted` with `{n: 2}` and
zero prover events.

**C. The website's simulated demo** (`docs/`, deployed by GitHub Pages): the
in-browser numeric skeptic is real code — "1 + 1 = 3" is refuted by exact
computation with no model involved, "every prime is odd" is refuted at n = 2 by
grid probing, Euler's n²+n+41 is caught at n = 40 — but the WebLLM
model-download/inference path needs a WebGPU browser to exercise. Open the Pages
site in Chrome/Edge, click "Load model", then run the "1+1=3" chip (must end
REFUTED — by computation) and the "n²+n is even" chip (must end "SIMULATED:
proved — NOT machine-checked"). Non-WebGPU browsers get a visible fallback pointing
to the recording. The site never prints an unqualified PROVED: certain outcomes are
only REFUTED (by computation); everything else is stamped simulated. Only this repo
with your key and a local Lean produces machine-checked results.

## Known-honest gaps

The demo scenario exercises the machinery, not mathematical ability — real proving
power comes from the models and Mathlib on your machine. The REPL backend
(`LEAN_MODE=repl`) has unit-level parsing coverage but its process management is
only exercised for real once you build the REPL in step A. Budgets are clamped to
≤16 at the API; raise the env defaults for long hunts.
