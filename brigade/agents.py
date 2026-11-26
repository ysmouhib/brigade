"""Stateless role-specific LLM agent calls for the proving brigade."""

from __future__ import annotations

import json

from . import prompts
from .llm import LLM, complete_json
from .models import ProofNode


async def skeptic_hj_query(llm: LLM, problem: str) -> dict:
    return await complete_json(
        llm,
        role="skeptic",
        system=prompts.SKEPTIC,
        user=f"PROBLEM:\n{problem}",
        temperature=0.1,
        max_tokens=600,
    )


async def brainstorm(llm: LLM, problem: str, persona: str, feedback: str) -> dict:
    user = f"PROBLEM:\n{problem}\n\nROUND FEEDBACK:\n{feedback or '(first round)'}"
    return await complete_json(
        llm,
        role="brainstormer",
        system=prompts.BRAINSTORMER.replace("{persona}", persona),
        user=user,
        temperature=0.8,
        max_tokens=1200,
    )


async def strategize(llm: LLM, problem: str, strategies: list[dict], feedback: str) -> dict:
    user = (
        f"PROBLEM:\n{problem}\n\nBRAINSTORMED STRATEGIES:\n"
        f"{json.dumps(strategies, indent=2)}\n\nROUND FEEDBACK:\n{feedback or '(first round)'}"
    )
    return await complete_json(
        llm,
        role="strategist",
        system=prompts.STRATEGIST,
        user=user,
        temperature=0.3,
        max_tokens=1800,
    )


async def formalize(
    llm: LLM,
    node: ProofNode,
    problem: str,
    errors: list[str],
    premises: list[str],
) -> dict:
    err_txt = "\n".join(errors) if errors else "(none)"
    prem_txt = "\n".join(f"- {p}" for p in premises) or "(none)"
    user = (
        f"PROBLEM:\n{problem}\n\n"
        f"TARGET lean_name: {node.lean_name}\n"
        f"INFORMAL STATEMENT:\n{node.informal}\n\n"
        f"SKETCH:\n{node.sketch}\n\n"
        f"AVAILABLE HJBrigade PREMISES:\n{prem_txt}\n\n"
        f"PREVIOUS LEAN ERRORS:\n{err_txt}"
    )
    return await complete_json(
        llm,
        role="formalizer",
        system=prompts.FORMALIZER,
        user=user,
        temperature=0.2,
        max_tokens=1000,
    )


async def prove(
    llm: LLM,
    node: ProofNode,
    helpers: list[ProofNode],
    errors: list[str],
    hint: str,
    premises: list[str],
    temperature: float = 0.25,
) -> dict:
    helper_txt = "\n".join(f"- {h.lean_statement}" for h in helpers) or "(none)"
    err_txt = "\n".join(errors) if errors else "(none)"
    prem_txt = "\n".join(f"- {p}" for p in premises) or "(none)"
    goal_txt = f"\nELABORATED LEAN GOAL:\n{node.goal}\n" if node.goal else ""
    user = (
        f"TARGET lean_name: {node.lean_name}\n"
        f"PINNED STATEMENT (do not restate or alter):\n{node.lean_statement}\n"
        f"{goal_txt}\n"
        f"VERIFIED HELPER LEMMAS:\n{helper_txt}\n\n"
        f"RELEVANT HJBrigade PREMISES:\n{prem_txt}\n\n"
        f"SKETCH:\n{node.sketch}\n\n"
        f"PREVIOUS LEAN ERRORS:\n{err_txt}\n\n"
        f"CRITIC HINT:\n{hint or '(none)'}"
    )
    return await complete_json(
        llm,
        role="prover",
        system=prompts.PROVER,
        user=user,
        temperature=temperature,
        max_tokens=2000,
    )


async def critique(llm: LLM, node: ProofNode, body: str, errors: list[str]) -> dict:
    user = (
        f"TARGET lean_name: {node.lean_name}\n"
        f"STATEMENT:\n{node.lean_statement}\n\n"
        f"FAILED PROOF BODY:\n{body}\n\n"
        f"LEAN ERRORS:\n" + "\n".join(errors)
    )
    return await complete_json(
        llm,
        role="critic",
        system=prompts.CRITIC,
        user=user,
        temperature=0.2,
        max_tokens=700,
    )


async def decompose(llm: LLM, node: ProofNode, history: list[str]) -> dict:
    user = (
        f"STUCK LEMMA: {node.lean_name}\n"
        f"STATEMENT:\n{node.lean_statement}\n"
        f"INFORMAL:\n{node.informal}\n\n"
        f"ERROR HISTORY:\n" + "\n".join(history[-6:])
    )
    return await complete_json(
        llm,
        role="decomposer",
        system=prompts.DECOMPOSER,
        user=user,
        temperature=0.4,
        max_tokens=1400,
    )
