#!/usr/bin/env bash
# Sets up the pinned Lean 4 + Mathlib project (and optionally the Lean REPL) that
# Brigade uses as its verifier. Run this ON YOUR MACHINE (needs ~5-10 GB and network).
#
# Everything is pinned to ONE version triple so lean4 / mathlib4 / repl agree:
set -euo pipefail

PIN="${LEAN_PIN:-v4.15.0}"      # bump all three together; check the repl repo has this tag
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LEAN_DIR="$ROOT/lean"
PROJ="$LEAN_DIR/BrigadeLean"

echo "== Brigade Lean setup (pin: $PIN) =="

# 1. elan (Lean toolchain manager)
if ! command -v elan >/dev/null 2>&1; then
  echo "-- installing elan"
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
fi

# 2. project skeleton with pinned toolchain + Mathlib
mkdir -p "$PROJ/BrigadeLean"
cat > "$PROJ/lean-toolchain" <<EOF
leanprover/lean4:$PIN
EOF
cat > "$PROJ/lakefile.lean" <<EOF
import Lake
open Lake DSL

package brigadeLean

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "$PIN"

@[default_target]
lean_lib BrigadeLean
EOF
cat > "$PROJ/BrigadeLean/Basic.lean" <<'EOF'
-- Intentionally tiny: scratch files written by the server do `import Mathlib` themselves.
def brigadeReady : Bool := true
EOF
[ -f "$PROJ/BrigadeLean.lean" ] || echo 'import BrigadeLean.Basic' > "$PROJ/BrigadeLean.lean"

cd "$PROJ"
echo "-- resolving Mathlib $PIN (first run downloads a lot)"
lake update mathlib
echo "-- fetching prebuilt Mathlib oleans (much faster than compiling)"
lake exe cache get
echo "-- building the (tiny) local library"
lake build

# 3. smoke test: this is the exact code path FileLeanVerifier uses
SMOKE="$PROJ/.brigade_scratch"
mkdir -p "$SMOKE"
cat > "$SMOKE/Smoke.lean" <<'EOF'
import Mathlib
set_option maxHeartbeats 400000

theorem brigade_smoke (n : ℕ) : Even (n ^ 2 + n) := by
  have h : n ^ 2 + n = n * (n + 1) := by ring
  rw [h]
  exact Nat.even_mul_succ_self n
#print axioms brigade_smoke
EOF
echo "-- smoke test (lake env lean) ..."
lake env lean "$SMOKE/Smoke.lean"
echo "   smoke test PASSED: Lean verified the demo theorem."

# 4. optional: the REPL backend (fast warm checks). Same pin.
if [ "${WITH_REPL:-1}" = "1" ]; then
  if [ ! -d "$LEAN_DIR/repl" ]; then
    echo "-- cloning leanprover-community/repl @ $PIN"
    git clone --depth 1 --branch "$PIN" https://github.com/leanprover-community/repl "$LEAN_DIR/repl" \
      || { echo "!! repl tag $PIN not found; clone manually and checkout a commit whose lean-toolchain matches"; exit 0; }
  fi
  ( cd "$LEAN_DIR/repl" && lake build )
  echo "-- REPL built: set LEAN_MODE=repl and LEAN_REPL_BIN=$LEAN_DIR/repl/.lake/build/bin/repl"
fi

echo "== done. Point the server at LEAN_PROJECT_DIR=$PROJ =="
