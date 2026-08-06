# Choose the countermodel search portfolio

Status: resolved
Type: prototype
Blocked by: 01, 07

## Question

Which ordered combination of exhaustive small magmas, structured magma families,
constraint-propagating backtracking, and deterministic pseudo-random candidates
delivers the best new FALSE-certificate coverage per work unit, and what state
should those searches share?

## Comments

- Prototype evidence: [Countermodel portfolio prototype results](../prototypes/countermodel-portfolio-results.md), backed by the runnable [throwaway prototype](../prototypes/countermodel_portfolio.py). Awaiting the required HITL reaction before recording the answer and resolving this ticket.
- The human accepted the proposed portfolio on 2026-08-04.

## Answer

Use one opaque, deterministic countermodel-portfolio strategy session. Its
private candidate order is:

1. exhaust every magma table of order 2, then every table of order 3;
2. enumerate structured families at orders 4 through 7;
3. run constraint-propagating backtracking at order 4, seeded by premise-models
   retained from structured search;
4. omit pseudo-random table sampling.

The scheduler sees only the existing countermodel `StrategySession` interface
and generic effort slices. It does not register or schedule these stages as
separate strategies, select magma orders, inspect retained models, or supply
stage-specific limits. This keeps portfolio ordering and cross-stage reuse
behind one deep module interface while preserving deterministic pause/resume
behavior.

### Ordered stages

The order-2 and order-3 exhaustive streams come first. On the 145 FALSE cases in
the development benchmark they found 6 and 34 first witnesses respectively.
Putting structured search before order-3 exhaustion preserved pre-backtracking
coverage but increased equation-assignment checks from roughly 20.8 million to
33.9 million in the controlled prototype, because larger magmas cost much more
to validate even when fewer tables are generated.

Structured search starts at order 4 because lower orders are already exhausted.
Within each order it uses one fixed versioned sequence: constants and
projections; min/max and additive/subtractive tables; affine tables; diagonal
and band families; product-affine tables; then projection-exception tables.
Orders advance from 4 through 7. Exact table deduplication removes overlaps
within and across families before premise evaluation.

After the structured stream, backtracking begins at order 4 with row-major cell
order and deterministic value order. It prunes a partial table as soon as a
fully evaluable premise assignment fails. Higher-order backtracking is not part
of the initial portfolio: it may be added as a versioned extension only if the
scheduler and benchmark decisions later show that its coverage justifies its
credits. A found table is yielded as a candidate; if central validation or the
judge rejects it, the unchanged session resumes from the next deterministic
search state.

### Shared search state

The portfolio session owns exactly the cross-stage state that earned measured
value:

- an exact set of canonical `(order, cells)` table identities, preventing the
  same table from being evaluated twice;
- the first four distinct structured premise-models at each order, retained in
  stream order;
- the current stage, generator cursor, backtracking stack, cumulative credits,
  and per-stage work counters needed to resume without replay or reordering.

A premise-model is a finite magma that satisfies the premise whether or not it
falsifies the goal. For order-4 backtracking, each cell tries the values appearing
in the retained order-4 premise-models, in retained-model order, followed by the
remaining values in ascending order. This changes traversal order without
removing any branch. In the controlled 2,000-node prototype slice it added two
FALSE cases (`hard1_0001` and `hard1_0024`) and reduced total visited
backtracking nodes from 106,558 to 102,675, with no losses.

Do not share heterogeneous partial frontiers, scheduler-visible search knobs,
wall-clock observations, expected labels, problem-pair oracle metadata, judge
feedback, or mutable state across Solo processes. The kernel continues to own
canonical problem terms, candidate evidence deduplication, exhaustive final
countermodel validation, certificate rendering, and judge transport.

### Credits and reproducibility

Each stage consumes credits only at deterministic checkpoints: table generation,
equation-assignment evaluation, and backtracking-node expansion. The exact
conversion of these counters into scheduler slices belongs to [Define
deterministic scheduler and budget accounting](04-define-deterministic-scheduler-and-budget-accounting.md),
but changing a hard deadline may only pause the stream; it may not alter stage,
family, table, cell, or value order.

Hash-derived pseudo-random candidates are excluded even though their bytes can
be reproduced. They are still sampling, which conflicts with the settled
deterministic-strategy contract, adds a strategy-version-sensitive seed surface,
and cannot report a finite search space exhausted. As supporting evidence, the
prototype tried 46,000 such candidates across the final 46-case residue and
added no witness.

### Acceptance evidence and limits

The selected exhaustive-first, seeded portfolio found countermodels for 99 of
145 development FALSE cases: 6 first found at order 2, 34 at order 3, 38 by
structured families, and 21 by seeded backtracking. Its output summary was
byte-identical across repeated runs. These public order-at-most-four results
choose the initial mechanism and guard against regressions; they do not establish
generalization to held-back order-five equations. Production strategy acceptance
still requires the paired, oracle-disabled judge benchmark defined by [Define the
benchmark and observability contract](07-define-benchmark-and-observability-contract.md).
