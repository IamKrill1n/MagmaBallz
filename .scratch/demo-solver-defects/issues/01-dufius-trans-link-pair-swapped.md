# `_try_auto_proof`'s plain `trans` row has its link pair swapped

Status: ready-for-human
Type: task
File: `examples/solo/demos/dufius/EQT02-S00007.py`, line ~2952

## Summary

Of the four two-hop chain orientations `_try_auto_proof` tries, row 1 — the plain
`(h s).trans (h t)` shape with no `.symm` — has its joint check wired to the wrong
pair of terms. It is written `(L1, R1)`; it should be `(R1, L1)`. Rows 2, 3 and 4
are correct.

## Mechanism

A two-hop chain `(h sigma).trans (h tau)` imposes three constraints:

1. `sigma(L1) = L2` — left end
2. `tau(R1) = R2` — right end
3. `sigma(R1) = tau(L1)` — the joint (this shared expression is M)

Constraints 1 and 2 are matching problems solved against the goal's two ends.
Constraint 3 has no unknowns left, so it is a structural-equality *check*, not a
solve. M is never searched for — each half computes a candidate midpoint and the
check asks whether they agree.

The rule is: whichever side of the assumption matches the goal, the *other* side is
the midpoint end.

| # | Shape | sigma from | tau from | correct joint |
|---|---|---|---|---|
| 1 | `(h s).trans (h t)` | L1~L2 | R1~R2 | `s(R1) = t(L1)` |
| 2 | `(h s).trans (h t).symm` | L1~L2 | L1~R2 | `s(R1) = t(R1)` |
| 3 | `(h s).symm.trans (h t)` | R1~L2 | R1~R2 | `s(L1) = t(L1)` |
| 4 | `(h s).symm.trans (h t).symm` | R1~L2 | L1~R2 | `s(L1) = t(R1)` |

Row 1 as written yields `s(L1)` vs `t(R1)` — row 4's condition. By construction
those are just `L2` and `R2`, so the check tests whether the goal's own two sides
are identical.

## Repro

```python
# assumption: x * y = (y * x) * y
# goal:       a * b = (b * (b * a)) * b
# valid proof: (h a b).trans (h (b*a) b)
sigma(R1) = ((b*a)*b)
tau(L1)   = ((b*a)*b)
  joint sigma(R1)==tau(L1)?          True     <- the chain is valid
  what the code actually compares?   False    <- wrong pair
_try_auto_proof -> None
```

With only that row's pair swapped to `(R1, L1)`:

```
_try_auto_proof -> ('intro a b\n  exact (h a b).trans (h (b*a) b)', '2_trans')
```

## Impact

The most natural two-hop shape — no `.symm` anywhere — never fires. Everything
reaching it falls through to brute force and then the LLM.

Second-order: when the goal is reflexive, the broken check *passes* and a
certificate is emitted without the real joint ever being verified — likely
ill-typed, costing a judge call. The X1 rule that properly handles reflexive goals
sits at Layer 1, which runs *after* this detector.

## A limitation that survives the fix

Matching `L1` against `L2` only binds variables occurring in `L1`. If the assumption
has a variable appearing only on its right side, sigma leaves it unbound and
`sigma(R1)` still contains a loose variable — at which point the joint is an
equation to *solve*, not an identity to check. Verified:

```python
# assumption: x = y * x ,  goal: a = c * (b * a)
# valid chain exists: (h a b).trans (h (b*a) c)
sigma = {x: a}          # y never bound
sigma(R1) = (y*a)       tau(L1) = (b*a)
-> None   (even on the link-corrected build)
```

Concrete improvement, separable from the one-line fix: at the joint, *match*
`sigma(R1)` against `tau(L1)` instead of testing equality. Then `y` binds to `b`
and the chain goes through.

Other limits, not fixable within this design: depth capped at two; both matches are
against the whole side, so rewrites inside a subexpression are invisible
(`match(x*x, (a*a)*b) = None`, verified); no derived lemmas; matching is exact with
no normalization.

## Proposed change

Swap row 1's link pair to `(R1, L1)`. One line. The joint-matching improvement above
is a separate, larger change and should be its own ticket if wanted.

## Comments

- 2026-07-26 — Filed from the survey in `SOLVER_COMPENDIUM.md` Part II §4. Verified
  by patching and re-running; no change has been committed to the demo file.
