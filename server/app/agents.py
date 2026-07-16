"""Agent layer: each function is one role in the brigade making one structured LLM call.

Agents are deliberately stateless; all state (the proof ledger) lives with the Chef in
orchestrator.py. That keeps the hierarchy auditable: every decision is an event, every
"fact" must pass through the Lean verifier.
"""
from __future__ import annotations
from . import prompts
from .llm import LLM, complete_json
from .models import ProofNode


async def brainstorm(llm: LLM, problem: str, persona: str, feedback: str) -> dict:
    user = f"PROBLEM:\n{problem}\n\nROUND FEEDBACK (may be empty):\n{feedback or '(first round)'}"
    return await complete_json(llm, role="brainstormer",
                               system=prompts.BRAINSTORMER.format(persona=persona),
                               user=user, temperature=0.9, max_tokens=1600)


async def skeptic(llm: LLM, problem: str) -> dict:
    return await complete_json(llm, role="skeptic", system=prompts.SKEPTIC.format(),
                               user=f"PROBLEM:\n{problem}", temperature=0.4, max_tokens=1200)


async def strategize(llm: LLM, problem: str, strategies: list[dict], feedback: str) -> dict:
    import json
    user = (f"PROBLEM:\n{problem}\n\nBRAINSTORMED STRATEGIES:\n"
            f"{json.dumps(strategies, indent=2, ensure_ascii=False)}\n\n"
            f"ROUND FEEDBACK:\n{feedback or '(first round)'}")
    return await complete_json(llm, role="strategist", system=prompts.STRATEGIST.format(),
                               user=user, temperature=0.4, max_tokens=2500)


async def formalize(llm: LLM, node: ProofNode, problem: str, errors: list[str],
                    retrieved: list[str] | None = None) -> dict:
    err = "\n".join(errors) if errors else "(none)"
    hints = ("\n\nPOSSIBLY RELEVANT MATHLIB DECLARATIONS (advisory, verify names):\n"
             + "\n".join(f"- {r}" for r in retrieved)) if retrieved else ""
    user = (f"ORIGINAL PROBLEM (context):\n{problem}\n\n"
            f"TARGET lean_name: {node.lean_name}\n"
            f"INFORMAL STATEMENT:\n{node.informal}\n\nSKETCH:\n{node.sketch}\n\n"
            f"PREVIOUS LEAN ERRORS ON THE STATEMENT:\n{err}{hints}")
    return await complete_json(llm, role="formalizer", system=prompts.FORMALIZER.format(),
                               user=user, temperature=0.2, max_tokens=1200)


async def prove(llm: LLM, node: ProofNode, helpers: list[ProofNode],
                errors: list[str], hint: str,
                retrieved: list[str] | None = None,
                temperature: float = 0.3) -> dict:
    helper_txt = "\n".join(f"- {h.lean_statement}" for h in helpers) or "(none)"
    err = "\n".join(errors) if errors else "(none)"
    goal = f"\nLEAN GOAL STATE (from the statement gate):\n{node.goal}\n" if node.goal else ""
    hints = ("\nPOSSIBLY RELEVANT MATHLIB DECLARATIONS (advisory, verify names):\n"
             + "\n".join(f"- {r}" for r in retrieved) + "\n") if retrieved else ""
    user = (f"TARGET lean_name: {node.lean_name}\n"
            f"PINNED STATEMENT (do not restate or alter):\n{node.lean_statement}\n{goal}\n"
            f"VERIFIED HELPER LEMMAS you may cite by name:\n{helper_txt}\n{hints}\n"
            f"INFORMAL SKETCH:\n{node.sketch}\n\n"
            f"PREVIOUS LEAN ERRORS:\n{err}\n\nCRITIC HINT:\n{hint or '(none)'}")
    return await complete_json(llm, role="prover", system=prompts.PROVER.format(),
                               user=user, temperature=temperature, max_tokens=2500)


async def critique(llm: LLM, node: ProofNode, body: str, errors: list[str]) -> dict:
    user = (f"TARGET lean_name: {node.lean_name}\nSTATEMENT:\n{node.lean_statement}\n\n"
            f"FAILED PROOF BODY:\n{body}\n\nLEAN ERRORS:\n" + "\n".join(errors))
    return await complete_json(llm, role="critic", system=prompts.CRITIC.format(),
                               user=user, temperature=0.2, max_tokens=900)


async def decompose(llm: LLM, node: ProofNode, history: list[str]) -> dict:
    user = (f"STUCK LEMMA lean_name: {node.lean_name}\nSTATEMENT:\n{node.lean_statement}\n"
            f"INFORMAL:\n{node.informal}\n\nERROR HISTORY:\n" + "\n".join(history[-6:]))
    return await complete_json(llm, role="decomposer", system=prompts.DECOMPOSER.format(),
                               user=user, temperature=0.5, max_tokens=1500)


async def retrospective(llm: LLM, problem: str, failures: str) -> dict:
    user = f"PROBLEM:\n{problem}\n\nWHAT FAILED THIS ROUND:\n{failures}"
    return await complete_json(llm, role="chef", system=prompts.CHEF_RETROSPECTIVE.format(),
                               user=user, temperature=0.4, max_tokens=800)


async def final_report(llm: LLM, problem: str, outcome: str) -> dict:
    user = f"PROBLEM:\n{problem}\n\nOUTCOME FACTS (from the verifier, trust these):\n{outcome}"
    return await complete_json(llm, role="chef", system=prompts.CHEF_REPORT.format(),
                               user=user, temperature=0.3, max_tokens=800)
