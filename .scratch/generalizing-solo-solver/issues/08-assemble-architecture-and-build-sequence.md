# Assemble the architecture and build sequence

Status: resolved
Type: prototype
Blocked by: 04, 05, 06, 07

## Question

How should the resolved kernel, search portfolios, scheduler, validation policy,
oracle subsystem, and benchmark be assembled into one implementation-ready
architecture and staged build sequence that remains within the Solo submission
contract?

## Comments

- Prototype proposal: [Generalized Solo solver architecture](../prototypes/architecture-prototype.md), backed by the interactive [runtime model](../prototypes/architecture_prototype.py) and its pure [architecture state model](../prototypes/architecture_model.py). Awaiting the required HITL reaction before recording the answer and resolving this ticket.
- The human accepted direct single-file development, with a generated bundler deferred unless measured maintenance or size pressure justifies it, on 2026-08-05.

## Answer

Build the first version directly as one sectioned `solver.py`. Treat its five
sections as deep modules with explicit interfaces, but do not add a source
flattener or runtime companion files. This keeps every development stage under
the actual Solo import, startup, protocol, and 500 KB source constraints. A
generated bundler may be reconsidered only if the direct file creates measured
maintenance or size problems.

The accepted planning artifact is the [Generalized Solo solver
architecture](../prototypes/architecture-prototype.md). Its interactive runtime
model exercised disabled, cache-hit, direction-hint, invalid-oracle, candidate
rejection, judge rejection, acceptance, exhaustion, and cutoff paths.

### Module architecture

The physical file is ordered from foundations to entry point:

1. solver kernel;
2. oracle subsystem and embedded artifact;
3. strategy implementations and stable registry;
4. case engine; and
5. stdin/stdout adapter and `main`.

Dependencies point downward only. Strategies and the oracle may depend on
canonical kernel values and pure kernel operations. They may not call or inspect
the case engine, scheduler, judge exchange, recorder, or each other.

The **solver kernel** exposes immutable semantic values plus two main operations:

```text
parse_problem(public_problem) -> Problem
admit(problem, candidate, limits, seen) -> Admission
```

Parsing, canonicalization, matching, substitution, evaluation, derivation
replay, evidence and request fingerprints, Lean rendering, source-policy checks,
and byte limits stay behind that interface. `Admission` is `rejected`,
`duplicate`, or `judge_request`; it never claims mathematical acceptance.

The **strategy registry** exposes only the settled lifecycle:

```text
registered_strategies() -> tuple[Strategy, ...]
Strategy.open(problem) -> StrategySession
StrategySession.advance(EffortBudget) -> AdvanceResult
```

Its stable initial order is the opaque countermodel portfolio followed by closed
forms, short chains, specialized synthesis, and bidirectional rewriting.
Registration is the only enable/disable seam used by paired benchmarks. Search
stages, tuning, frontiers, retained premise-models, and term pools remain private
session state.

The **oracle subsystem** keeps its previously settled interface:

```text
OracleSubsystem(mode, artifact_bytes).consult(
    problem, eq1_id, eq2_id
) -> OracleResult
```

Disabled mode structurally bypasses the artifact and pair IDs. Enabled mode
hides decoding, content binding, indexes, shared magma pools, proof recipes, and
corruption handling. Cached evidence travels through ordinary kernel admission
and judging. Invalid or rejected cached evidence clears its associated first-turn
hint before reasoning opens.

The **case engine** is the deep orchestration module:

```text
run_case(start_message, judge_exchange, trace_recorder) -> CaseOutcome
```

It derives monotonic deadlines once, parses the problem, consults the oracle
once, processes a cache candidate, opens the stable registry, grants hierarchical
one-credit scheduler turns, synchronously admits and judges every yield, records
dispositions, and stops on acceptance, judge infrastructure error, exhaustion,
or cutoff. The scheduler stays inside this module; no production caller needs a
separate scheduling interface. Pure transition functions remain available at
internal seams for tests.

`judge_exchange(verdict, source) -> JudgeResult` is a real seam with a
line-delimited stdin/stdout adapter in production and a scripted in-memory
adapter in tests. `trace_recorder(record)` has tagged-stderr and in-memory
adapters. The benchmark tooling must consume tagged stderr incrementally rather
than rely on the proxy's bounded final stderr tail; this never adds a solver
stdout message or feeds telemetry back into search.

The **protocol adapter** owns JSON transport and no solving policy. `PROMPT` is
empty and no LLM call exists. The executable `pipeline/proxy.py` and the README
make an accepted judge response terminal; they do not implement the separate
`submit` step still described in `docs/solo_mode.md`. The solver therefore exits
after the case engine stops and never fabricates an unverified fallback. All
timeout and certificate-size limits come from the startup message. A 300-second
benchmark selects the versioned 30-second judge-start window and 2-second
shutdown margin without making wall time a search input.

### Runtime assembly

```text
startup
  -> kernel.parse_problem
  -> oracle.consult
  -> optional cached candidate -> kernel.admit -> judge_exchange
  -> strategy_registry.open
  -> case engine selects one session and grants one credit
  -> session.advance
  -> optional candidate -> kernel.admit -> judge_exchange
  -> repeat or stop
```

Only judge acceptance solves the case. Local rejection, ordinary judge
rejection, strategy fault, and oracle failure never become verdicts and never
send feedback into an unchanged strategy session.

### Staged build sequence

Every stage leaves the single-file solver runnable, reports its exact UTF-8
source size, and runs narrow contract tests before benchmarks:

1. **Submission spine:** empty `PROMPT`, startup decoding, monotonic profile,
   stdout-only judge exchange, tagged-stderr tracing, and source/certificate byte
   guards. Lock the actual accepted-judge terminal behavior and absence of LLM or
   `submit` calls.
2. **Kernel vertical slice:** canonical terms/problems, derivations, finite
   magmas, admission, renderers, fingerprints, and limits. Send one structured
   TRUE fixture and one checked FALSE fixture through the real proxy and judge.
3. **Case engine:** port the accepted scheduler model with scripted sessions;
   cover pause, yield, exhaust, fault, rejection, acceptance, infrastructure
   error, and cutoff. Remove scripted registrations before coverage runs.
4. **Countermodel portfolio:** add exhaustive orders two and three, structured
   orders four through seven, and seeded order-four backtracking behind one
   session. Verify deterministic pause/resume prefixes and run the
   FALSE-stratified development gate.
5. **Proof strategies:** add closed forms, short chains, specialized synthesis,
   and bidirectional rewriting one at a time. Require replayable derivation DAGs,
   deterministic prefixes, and an oracle-disabled paired development pass before
   enabling the next. Keep any `lean_body` sweep provisional and separate.
6. **Composition benchmark:** run repeat smoke cases plus paired 30/300-second
   development runs with both lanes. Verify non-starvation, synchronous judge
   order, no baseline losses, stable trace projections, cutoff behavior, and
   source-size reports.
7. **Oracle contracts:** first prove disabled behavior is identical for absent,
   corrupt, and different artifacts. Then add content-bound cache and first-turn
   direction fixtures, including rejection clearing the hint, without changing
   reasoning registration or behavior.
8. **Artifact and hardening:** inventory reusable accepted evidence, choose
   compression against the measured remaining source budget, embed versioned
   bytes, and finish with enabled diagnostics, oracle-disabled acceptance, the
   complete Solo harness, duplicate smoke runs, differing-case repeats, and all
   source/certificate size gates.

The build deliberately postpones corpus compression until the reasoning engine
reveals both the reusable artifact inventory and the actual remaining byte
budget. Any proof mechanism beyond the initial rewrite portfolio likewise waits
for measured residual coverage rather than entering the first architecture
speculatively.
