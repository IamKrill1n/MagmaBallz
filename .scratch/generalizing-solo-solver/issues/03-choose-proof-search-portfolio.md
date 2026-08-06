# Choose the proof search portfolio

Status: resolved
Type: prototype
Blocked by: 01, 07

## Question

Which ordered combination of closed-form synthesizers, substitution and
short-chain unification, specialized algebraic engines, and bidirectional
subterm-rewrite search delivers complementary TRUE-certificate coverage, and
what proof representation can reconstruct every accepted result reliably?

## Answer

Use a four-lane deepening portfolio in this initial priority order:

1. closed-form synthesis;
2. substitution and short-chain unification;
3. specialized algebraic synthesis; and
4. bidirectional subterm-rewrite search.

This is the proof lane's priority order, not permission to starve later search.
The deterministic scheduler may interleave resumable sessions after their first
slices, but must try the cheaper, more reliable proof families first and retain
the same candidate order for the same credit sequence.

### Closed-form synthesis

Start with bounded, structurally triggered synthesizers whose search spaces can
be exhausted cheaply:

- reflexivity in the goal's required orientation;
- singleton collapse when the premise equates an arbitrary carrier element to
  a term independent of it; and
- direct one-sided-variable constancy, including a congruence wrapper when the
  differing expression occurs under one application node.

Each trigger must verify the exact derived endpoints before yielding. A trigger
that merely suggests a likely Lean tactic is not a closed-form success.

### Substitution and short-chain unification

Next enumerate direct premise instantiations, first over goal variables and then
over a bounded canonical pool of goal subterms and small compound terms. Try
both premise orientations. Reuse those instantiations for one-hop and two-hop
chains and for one-congruence bridges.

Two-hop synthesis must implement all four orientation shapes. It must solve the
shared midpoint by extending the two substitutions with deterministic joint
unification; comparing partially substituted midpoint terms for equality is
insufficient when a premise variable occurs on only one side. Complete every
premise substitution before constructing a hypothesis node. Enumerate by proof
cost, term size, canonical term order, orientation, and substitution tuple so
the candidate stream is stable.

### Specialized algebraic synthesis

Then run narrowly triggered synthesizers for algebraic consequences that are
expensive or awkward to rediscover as blind short chains: repeated-variable
specialization, compound pivots, derived constancy lemmas, and collapse/spine
lemmas composed with congruence. These are separate strategies only where their
trigger and private search state differ materially; common matching,
substitution, and derivation construction stay in the kernel.

Specialized engines must construct the derived lemma and its uses as structured
equality evidence. Do not treat `simp`, `rw`, or another generated tactic body
as the engine's proof representation. Existing deterministic tactic sweeps may
remain behind the controlled `lean_body` candidate kind as a provisional port,
run after the structured portfolio and reported separately, but they are not a
substitute for a reconstructible specialized engine.

### Bidirectional subterm-rewrite search

Last, search for a collision between frontiers rooted at the two goal
endpoints. An edge applies either orientation of a completely instantiated
premise at one subterm position. Its evidence is the instantiated hypothesis
wrapped in one `congr` node per context level. Derived constancy edges are
allowed only when their complete two-hypothesis derivation is retained.

Expansion is deterministic and resumable: canonical term ordering, explicit
depth and term-size strata, stable substitution-pool growth, and abstract
credits for generated or admitted states. Frontier and parent maps are opaque
strategy-session state. A hard deadline may pause only at a checkpoint; it may
not skip an incomplete substitution or silently discard the rest of a stratum.
A collision joins the two parent traces with `symm` and `trans` rather than
emitting a preformatted `calc` block.

### Canonical proof representation

Every production lane yields the shared immutable `Derivation` DAG settled by
[Define the solver kernel and strategy interface](01-define-solver-kernel-and-strategy-interface.md):
`refl`, `hyp(total_substitution)`, `symm`, `trans`, and `congr`. Strategies build
this evidence during search; the kernel never attempts to parse a generated or
accepted Lean body back into a proof.

The renderer validates and topologically renders the DAG. It may flatten a
short unshared path into `calc`, while rendering shared or repeated subproofs as
named `have` bindings so a derived lemma is proved once rather than duplicated.
Endpoints are recomputed at every node, the root must equal the canonical goal,
and central validation and the judge remain authoritative. This representation
can express direct substitutions, short chains, nested subterm rewrites,
constancy arguments, and reusable derived lemmas without adding public
strategy-specific proof nodes.

A controlled `lean_body` remains exact source evidence rather than a
reconstructible derivation. Preserve its normalized bytes for judging and
observability, but label the producing strategy provisional until it emits a
`Derivation`; never claim to have reconstructed it after acceptance.

### Promotion and evidence

The [proof-portfolio prototype](../prototypes/proof_portfolio.py) confirmed the
interaction and failure policy: a normal-suite smoke slice produced one
judge-accepted singleton derivation; the first hard residuals remained
unresolved; generated specialized tactic bodies were rejected; and an existing
rewrite implementation's incomplete substitution raised `KeyError('z')`, which
the strategy seam isolated as a fault. These observations validate the shape,
not broad coverage.

Implement each lane behind an independently disabled strategy registration.
Promote it only through the paired development and acceptance comparisons in
[Define the benchmark and observability contract](07-define-benchmark-and-observability-contract.md):
at least one new judge-accepted case and no lost baseline cases at 300 seconds.
Report additions, judge cost, and unresolved residuals by concrete strategy and
candidate kind; use those measurements, not the ordering decision itself, to
decide whether equality saturation or derived-lemma search deserves a later
portfolio lane.
