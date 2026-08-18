# Equation 168 accounts for 100% of the extra_hard coverage residual

Status: ready-for-human
Type: task
Scope: solver capability (not a framework defect)

## Summary

On the full `evaluation_extra_hard` corpus (200 cases, 120 s, LLM disabled), the
strongest available solver scores 169/200. The 31 misses are **entirely**
problems whose hypothesis is Equation 168:

```
everything that is NOT eq168      161/161      100%
eq168                               8/39         21%
```

All 31 unsolved cases are FALSE-labelled. No non-eq168 problem in the corpus is
missed.

## The law

```
Equation 168 (hypothesis):   x = (y ◇ x) ◇ (x ◇ z)
```

74 of the 800 problems across the four `evaluation_*` corpora use it as the
hypothesis. Every one is FALSE. They cluster in the hard tiers: 39 `extra_hard`,
33 `hard`, 2 `normal`. Across the sampled sweep it is the hardest law by volume
at 9/30 accepted.

## This is a capability wall, not a budget wall

Three independent lines of evidence:

1. **Failures terminate early.** Against a 120 s cap, the 31 failures ran
   min 50 s / median 79 s / max 90 s. **Zero hit the timeout.** The solver
   exhausts its strategy portfolio and stops with budget still on the table.
2. **10x the budget converts nothing.** A separate 16-case eq168 run at 600 s
   produced the same 9/16 as shorter budgets. Every case that solves, solves in
   under 9 s.
3. **Two unrelated architectures fail identically.** On that 16-case set, a
   ~60 KB zero-LLM deterministic kernel (`examples/solo/demos/generalized`) and
   a ~482 KB LLM-steering solver agree case-for-case on all 16, with zero
   disagreements and the same seven unsolved. They share no code.

## The boundary is sharp

The eq168 cases that do solve all target low-numbered equations and finish in
2–4 s:

```
solved targets:   51, 54, 58, 68, 103, 106, 110, 116
failed targets:   3461 and above
```

This is not a search that nearly gets there. It cleanly solves small-target
instances and cleanly fails large-target ones, in contiguous blocks.

## Regression set

Every failure emits exactly 4 disproved certificates — 124 judge calls, 124
`incorrect`, no variance — so the dead-end path is deterministic and will
reproduce identically.

| case | target eq | judge calls | elapsed |
|---|---|---|---|
| `evaluation_extra_hard_0170` | 3461 | 4 | 64 s |
| `evaluation_extra_hard_0171` | 3462 | 4 | 57 s |
| `evaluation_extra_hard_0172` | 3463 | 4 | 73 s |
| `evaluation_extra_hard_0173` | 3521 | 4 | 64 s |
| `evaluation_extra_hard_0174` | 3522 | 4 | 64 s |
| `evaluation_extra_hard_0175` | 3523 | 4 | 80 s |
| `evaluation_extra_hard_0176` | 3532 | 4 | 81 s |
| `evaluation_extra_hard_0177` | 3533 | 4 | 82 s |
| `evaluation_extra_hard_0178` | 3534 | 4 | 81 s |
| `evaluation_extra_hard_0179` | 3535 | 4 | 90 s |
| `evaluation_extra_hard_0180` | 3864 | 4 | 64 s |
| `evaluation_extra_hard_0181` | 3883 | 4 | 73 s |
| `evaluation_extra_hard_0182` | 3915 | 4 | 66 s |
| `evaluation_extra_hard_0183` | 3921 | 4 | 80 s |
| `evaluation_extra_hard_0184` | 3952 | 4 | 63 s |
| `evaluation_extra_hard_0185` | 3958 | 4 | 74 s |
| `evaluation_extra_hard_0186` | 3989 | 4 | 81 s |
| `evaluation_extra_hard_0187` | 3997 | 4 | 80 s |
| `evaluation_extra_hard_0188` | 4001 | 4 | 87 s |
| `evaluation_extra_hard_0189` | 4268 | 4 | 67 s |
| `evaluation_extra_hard_0190` | 4282 | 4 | 80 s |
| `evaluation_extra_hard_0191` | 4314 | 4 | 64 s |
| `evaluation_extra_hard_0192` | 4315 | 4 | 80 s |
| `evaluation_extra_hard_0193` | 4339 | 4 | 80 s |
| `evaluation_extra_hard_0194` | 4357 | 4 | 86 s |
| `evaluation_extra_hard_0195` | 4587 | 4 | 63 s |
| `evaluation_extra_hard_0196` | 4606 | 4 | 50 s |
| `evaluation_extra_hard_0197` | 4615 | 4 | 79 s |
| `evaluation_extra_hard_0198` | 4645 | 4 | 74 s |
| `evaluation_extra_hard_0199` | 4666 | 4 | 80 s |
| `evaluation_extra_hard_0200` | 4689 | 4 | 90 s |
## Suggested next step

The question is mathematical, not a matter of tuning: what does a countermodel
for `x = (y ◇ x) ◇ (x ◇ z)` against a high-numbered target actually look like,
and is it reachable by finite-table search at all? Worth checking
`teorth/equational_theories` upstream before rediscovering it — Equation 168 is
a named law there and its refutation structure may already be known.

## Limits

- One solver on this corpus; the cross-architecture claim rests on the separate
  16-case eq168 run.
- Budgets of 120 s / 600 s are well below the Solo reference of 3600 s. The
  early-termination evidence is what rules out a longer run, not the budget
  itself.
- The 9.3% population figure covers the four `evaluation_*` corpora only, not
  `normal` / `hard1` / `hard2` / `hard3`.
