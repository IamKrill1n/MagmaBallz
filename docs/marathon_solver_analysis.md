# Marathon demo solver analysis

This synthesis covers every solver discovered under
`examples/marathon/demos`. Three independent reviews examined baseline +
few-shot, triage + M00005, and M00009 + M00010.

## Shared strategy

The runnable Marathon demos converge on the same broad funnel:

1. Search cheap finite countermodels across many problems.
2. Rank unresolved problems by a cheap difficulty proxy.
3. Spend LLM budget sequentially on the easiest-looking remainder.
4. Append answers immediately so budget termination preserves partial score.

Baseline implements only step 1. Triage and few-shot add generic LLM proofs.
M00009 adds a wider deterministic proof pass and proof-example transfer.
M00010 replaces the generic proof pass with the broadest specialized proof,
countermodel, completion, and e-graph portfolio.

## Differences worth taking

| Solver | Best idea | Important limitation |
| --- | --- | --- |
| baseline | Deterministic Fin 2–3 witnesses and durable writes | No true proofs or useful ordering |
| triage | Breadth-first cheap pass, then low/high effort passes | No local validation; retries lack feedback |
| fewshot | Bounded cross-problem proof examples | Syntactic checks can poison the example pool |
| M00005 | Layered waterfall, routed prompts, judge-feedback repair | Uses the Solo stdin protocol, so scores zero in Marathon as written |
| M00009 | Global deterministic proof passes and structural few-shot matching | Broken `lean --check` gate; unsafe fallback control flow |
| M00010 | Semantic ranking, dynamic row budgets, large mechanical portfolio, LLM as waypoint oracle | Mostly static knowledge; repeats work across effort tiers |

## Design selected for the submission

- Start from M00010-style solver-owned proof/countermodel reconstruction, not
  raw unvalidated LLM code.
- Sweep every problem with cached certificates, small countermodels, and cheap
  focused proofs before deep work.
- Rank later work by focused structural match, validated-example similarity,
  equation size/arity, and stable ID.
- Allocate time dynamically from remaining budget and unresolved count; keep
  a shutdown margin and cap individual rows.
- Admit only locally Lean-accepted true proofs to the few-shot pool.
- Feed exact mechanical/Lean failures into targeted retries and suppress exact
  duplicate actions.
- Keep immediate flushed output and deterministic seeds.
- Add breadth-first cost bands in later versions so an expensive row cannot
  monopolize a phase; avoid rerunning completed search engines.

The locked benchmark is deliberately token-free, so it measures the native
foundation and scheduler. Token-enabled evaluation remains necessary before
claiming that LLM routing or within-run learning improves the official track.
