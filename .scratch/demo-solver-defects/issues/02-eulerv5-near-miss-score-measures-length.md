# eulerv5 near-miss score measures length, not similarity

Status: ready-for-human
Type: task
File: `examples/solo/demos/eulerv5/solver.py`, line ~2155

## Summary

When `proof_bfs_v5`'s two frontiers fail to collide, the failure path harvests
"near-miss" expressions from the forward frontier and feeds the top 3 into the LLM
prompt. The score used to rank them does not measure similarity to the target — it
effectively measures the candidate's own length, so the ranking is longest-first.

## The code

```python
for nn in fwd:
    if nn in bwd: continue
    overlap = sum(1 for c in nn if c in target)
    if overlap > len(target) * 0.5:
        _last_bfs_near_misses.append((nn, overlap, total_states))
_last_bfs_near_misses.sort(key=lambda x: -x[1])
_last_bfs_near_misses = _last_bfs_near_misses[:5]
```

`sum(1 for c in nn if c in target)` counts, per character of the candidate, whether
that character occurs ANYWHERE in the target. The alphabet is only variable letters,
the operator, and parentheses — so almost every candidate scores its own full
length. Verified:

```
'(x-y)-x'              len= 7  overlap= 7
'(y-x)-y'              len= 7  overlap= 7
'((x-x)-(y-y))-(x-y)'  len=19  overlap=19
```

Two structurally unrelated expressions of equal length score identically, and a
large unrelated expression outscores an exact structural neighbour. Since the list
sorts by overlap descending, the ranking is effectively longest-first — and the
longest states are the deepest, most-rewritten ones, i.e. the least likely to be
near the goal. The `> len(target) * 0.5` threshold is likewise a length filter.

## Why it matters

The near-miss mechanism is the strongest idea in eulerv5's design: a failed
deterministic search hands the model a *partial result* (a proof that
`goal_left = E` already exists — replay the recorded rewrites), converting total
failure into a reduced problem, and the state count tells the model the cheap paths
are already exhausted. `_build_llm_hints` (line ~1499) injects the top 3, but only
when the oracle says the verdict is TRUE.

That mechanism is only as good as the ranking that selects which 3 the model sees.

## Impact

Bounded. Near-miss scores never affect correctness, only which hint the model sees —
anything that becomes a certificate still passes exact matching and then the judge.
Term size is also capped at 20 nodes, so the length bias has a ceiling.

## Two available fixes, both already in the file or the data structure

- `_string_overlap5` (line 2341) computes a longest-common-substring score and does
  measure shared structure. It already ranks `rw` chains; it is simply not used here.
- Depth-in-the-search is a better proxy for "close" than length. It is recoverable
  by walking `prev_norm` back to `start`, and the expansion loop
  (`for depth in range(max_depth)`) knows it while building — but it is neither
  stored per state nor used for ranking.

## Comments

- 2026-07-26 — Filed from the survey in `SOLVER_COMPENDIUM.md` Part II §5. Scoring
  degeneracy verified directly; no change has been committed to the demo file.
