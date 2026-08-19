# Define the solver kernel and strategy interface

Status: resolved
Type: grilling
Blocked by: none

## Question

What minimal shared term, problem, budget, candidate, and strategy interfaces
should hide parsing, substitution, evaluation, proof provenance, and certificate
rendering while allowing the strongest existing algorithms to be ported without
leaking their internal knobs into the scheduler?

## Answer

Use one deep, in-process solver kernel around immutable semantic values and a
two-stage strategy lifecycle. The scheduler interacts with registered strategies
and their opaque sessions; it never parses terms, examines evidence, renders
Lean, or supplies algorithm-specific tuning parameters.

### Shared values

- `Var(scope, slot, display_name)` and `App(left, right)` are the two immutable,
  hashable term variants. Variables are numbered by first occurrence separately
  in the premise and goal; `display_name` is non-semantic diagnostic metadata.
- `Equation(variables, lhs, rhs)` owns one variable scope and validates that both
  terms are well scoped.
- `Problem(premise, goal, fingerprint)` is the complete reasoning input. Its
  fingerprint is derived from the canonical equations. Corpus equation IDs and
  inbound run IDs remain transport/oracle metadata and are not visible to
  reasoning strategies.
- `FiniteMagma(order, cells)` stores an immutable row-major operation table and
  enforces square shape and value range.
- `Candidate(kind, payload, provenance)` is one class, not a subclass hierarchy.
  Its kind is `derivation`, `countermodel`, or `lean_body`.
- `AdvanceResult(status, candidate, credits_used, fault)` is one immutable
  result. Its status is `yielded`, `paused`, `exhausted`, or `fault`; at most one
  candidate is returned per advancement.

Hash-consing, memoized substitution/evaluation, packed table storage, and proof
DAG sharing are implementation choices hidden behind these values, not further
interfaces.

### Strategy lifecycle

```text
Strategy
  id
  version
  lane                 # proof | countermodel
  open(problem) -> StrategySession

StrategySession
  advance(EffortBudget) -> AdvanceResult
```

`Strategy` is a stateless registered search definition. `StrategySession` owns
all mutable state for that strategy on one problem. Concrete strategies satisfy
these protocols through composition rather than inheriting from a common base
class.

An `EffortBudget` supplies integer credits and a hard safety deadline.
Strategies consume credits at deterministic checkpoints. Each versioned
strategy privately maps credits to its table blocks, state expansions,
substitution attempts, or other work; depths, magma families, term pools, state
caps, and checkpoint granularity never enter scheduler configuration.

For a fixed canonical problem, strategy ID/version, private configuration, and
sequence of granted credits, a session must produce one stable ordered candidate
stream and terminal outcome. It may not use entropy, PRNG sampling,
wall-clock-directed branching, mutable external state, or unstable collection
iteration. The hard deadline may pause work at a safe checkpoint, but may not
skip or reorder candidates or report the search exhausted.

`yielded` pauses the session at its next candidate. `paused` means the logical
credit slice ended while work remains. `exhausted` means the deterministic
search space is complete. `fault` isolates an implementation defect so other
strategies can continue.

Strategies never call the judge and receive no local-validation result, judge
status, or Lean error. If a candidate is rejected, the scheduler advances the
unchanged session to obtain its next deterministic candidate. Error-directed
repair, if later justified, is a separate strategy rather than a callback on
every session.

### Proof and countermodel evidence

`Derivation` has safe factories for exactly five equational operations:

```text
refl(term)
hyp(total_premise_substitution)
symm(proof)
trans(first, second)
congr(left_proof, right_proof)
```

Each factory computes its endpoints and rejects an invalid construction
immediately. `trans` requires identical middle terms. `congr` combines proofs
of `a = a'` and `b = b'` into a proof of `a ◇ b = a' ◇ b'`; `refl` handles an
unchanged side. These primitives compose direct substitutions, short chains,
subterm rewrites, constancy arguments, singleton collapse, and bidirectional
rewrite traces without specialized public proof-node classes.

A countermodel payload is a `FiniteMagma`. Before it becomes judge-eligible, the
kernel exhaustively checks that the premise holds for every assignment and
retains a deterministic assignment showing that the goal fails.

The controlled `lean_body` payload is a tactic body only, never full certificate
source. It exists to port deterministic eulerv5-style tactic sweeps and existing
specialized emitters that do not yet produce a derivation. It is a provisional
candidate until Lean accepts it; deterministic generation alone does not imply
soundness.

### Kernel responsibilities

The kernel owns:

- parsing, operator normalization, variable scoping, and alpha-normalization;
- structural equality, matching, substitution, subterm traversal, and
  evaluation;
- safe derivation construction and endpoint checking;
- finite-magma shape, range, premise, and goal validation;
- candidate deduplication;
- full Lean certificate rendering, imports, binders, escaping, and size checks;
- judge transport and the distinction between a yielded candidate and a solved
  problem.

Candidate provenance is generated by the kernel rather than supplied
free-form by a strategy. It contains only `strategy_id`, `strategy_version`,
`candidate_index`, `cumulative_credits`, and `evidence_fingerprint`.
Strategy-specific search knobs do not leak through provenance.

Only a judge-accepted rendered certificate solves the problem. Structured
derivations and exhaustively checked countermodels should have high acceptance,
but the judge remains authoritative for renderer, elaboration, resource, and
policy failures.

### Class and module shape

The value and lifecycle classes that earn their place are `Var`, `App`,
`Equation`, `Problem`, `FiniteMagma`, `Derivation`, `Candidate`,
`EffortBudget`, `AdvanceResult`, `Strategy`, and `StrategySession`. Parsing,
matching, substitution, evaluation, candidate validation, and certificate
rendering remain focused functions in the deep kernel module.

Do not introduce separate parser, renderer, validator, provenance-manager, or
per-proof-rule public classes without a second implementation or measured need.
This keeps the interface small while centralizing the duplicated representations
and certificate machinery found in the existing solvers.

### Porting existing mechanisms

- suii0x and dufius structural matchers port to the shared terms and safe
  derivation factories.
- eulerv5/opnorm rewrite searches retain opaque frontier state in sessions and
  turn successful traces into derivation DAGs.
- Exhaustive, structured-family, and backtracking countermodel searches retain
  private enumeration state and yield `FiniteMagma` values.
- Deterministic tactic sweeps use restricted `lean_body` candidates.
- Existing unseeded or seeded-random sampling and wall-clock-selected search
  prefixes are not ported; deterministic enumeration replaces them.
