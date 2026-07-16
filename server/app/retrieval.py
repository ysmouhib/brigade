"""Optional Mathlib premise retrieval (RETRIEVAL=loogle|leansearch, default off).

State-of-the-art Lean agents condition generation on retrieved Mathlib lemmas; for a
general-purpose LLM the dominant failure mode is guessing lemma names. This module is
best-effort by design: any network error, timeout, or shape change returns [] and the
pipeline continues without hints. Results are advisory text for prompts only — they
never touch the acceptance path.
"""
from __future__ import annotations
import httpx

_TIMEOUT = httpx.Timeout(8.0)


async def search(backend: str, query: str, k: int = 6,
                 client: httpx.AsyncClient | None = None) -> list[str]:
    """Return up to k 'name : type' strings from the chosen backend, or [] on any failure."""
    if backend not in ("loogle", "leansearch") or not query.strip():
        return []
    own = client is None
    client = client or httpx.AsyncClient(timeout=_TIMEOUT)
    try:
        if backend == "loogle":
            r = await client.get("https://loogle.lean-lang.org/json", params={"q": query})
            r.raise_for_status()
            hits = (r.json() or {}).get("hits", []) or []
            return [f"{h.get('name', '?')} : {h.get('type', '')}".strip() for h in hits[:k]]
        r = await client.post("https://leansearch.net/api/search",
                              json={"query": [query], "num_results": k})
        r.raise_for_status()
        data = r.json()
        # leansearch returns a list (per query) of lists of {result: {name, formal_type|statement}}
        first = data[0] if isinstance(data, list) and data else []
        out = []
        for item in first[:k]:
            res = item.get("result", item) if isinstance(item, dict) else {}
            name = res.get("name") or "?"
            typ = res.get("formal_type") or res.get("statement") or ""
            out.append(f"{name} : {typ}".strip())
        return out
    except Exception:  # noqa: BLE001 — retrieval is strictly best-effort
        return []
    finally:
        if own:
            await client.aclose()
