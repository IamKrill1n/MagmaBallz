# Solvers submit countermodels the judge disproves, without a local pre-check

Status: ready-for-human
Type: task
Scope: solver behaviour (not a framework defect)

## Summary

Across the 400-case baseline sweep, four of five solvers submitted certificates
the judge returned `incorrect` on — a countermodel the judge actively disproves,
not a solver that found nothing:

| solver | accepted / 80 | disproved certificates |
|---|---|---|
| `reja23` | 77 | 12 |
| `reja22` | 76 | 40 |
| `m00006` | 56 | 24 |
| `generalized` | 53 | **0** |
| `suii0x` | 32 | 49 |

`generalized` is the outlier because it re-checks a countermodel locally before
admitting it (`validate_countermodel` — evaluate both equations over the
candidate table, confirm the premise holds and the conclusion fails). The others
submit and let the judge decide.

## Why it matters

Solo scores only `accepted` (`docs/solo_mode.md`), so a disproved certificate
costs no points directly. It costs time, and it costs it precisely where the
budget is scarcest:

- On `evaluation_extra_hard_0191`, `reja22` spent 81 s across **11 judge calls,
  all disproved**, and solved nothing.
- On the 31-case eq168 residual, the strongest solver spent 124 judge calls
  producing 124 disproved certificates.
- Each judge call is a Lean compile with a 300 s ceiling
  (`pipeline/config.json`).

At the 60–120 s budgets measured here that is wasteful. At the Solo reference of
3600 s it is the difference between exploring one dead end and exploring many.

## The fix

Validate before submitting: evaluate the premise and conclusion over the
candidate finite table in Python, and only call the judge when the premise holds
everywhere and the conclusion fails somewhere. This is cheap — the tables are
small — and the reference implementation is already in this repo at
`examples/solo/demos/generalized/solver.py`.

## Caveat

`generalized`'s zero is partly a consequence of it being more conservative
overall — it also produces the most "no candidate at all" outcomes (7 of 16 on
the eq168 set, spending 568 s and issuing zero judge calls). Suppressing bad
submissions is worth doing on its own terms; it should not be assumed to carry
`generalized`'s coverage with it, which is lower than the reja line's.

## Evidence

`results/nollm.jsonl` (400 cases, judge statuses per case),
`results/eq168.jsonl` (16 cases), `results/xh_full.jsonl` (200 cases).
Re-tabulate with `harness/analyze.py`.
