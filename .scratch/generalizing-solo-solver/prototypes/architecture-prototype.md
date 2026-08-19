# PROTOTYPE — Generalized Solo solver architecture

Question: does this module shape and staged build sequence assemble the resolved
kernel, portfolios, scheduler, admission policy, oracle, and benchmark without
creating cross-module knowledge or violating the one-file Solo contract?

This is planning evidence for **Assemble the architecture and build sequence**.
It is not a production solver. Drive the accompanying runtime model from the
repository root with:

```bash
python3 .scratch/generalizing-solo-solver/prototypes/architecture_prototype.py
```

Run its fixed edge-case tour with:

```bash
python3 .scratch/generalizing-solo-solver/prototypes/architecture_prototype.py --batch
```

## Proposed production shape

Develop the first version directly as the final `solver.py`, divided into
explicit sections. Do not add a source flattener yet. The single source stays
continuously runnable under the same import, source-size, startup, and protocol
constraints as the submitted artifact. The sections are modules in the design
sense: each has an interface and hides its implementation even though all live
in one physical file.

```text
stdin/stdout adapter
        |
        v
case engine -------------------------------------> judge exchange
   |                 |                  |
   v                 v                  v
oracle subsystem  strategy registry  solver kernel
   |                 |                  ^
   |                 +------------------+
   +------------------------------------+
```

Dependency arrows point from caller to dependency. Strategies and the oracle
may use canonical kernel values and pure kernel operations. They never import or
call the case engine, scheduler, judge exchange, or trace recorder.

### Solver kernel

Interface:

```text
parse_problem(public_problem) -> Problem
admit(problem, candidate, limits, seen) -> Admission
```

The immutable term, equation, magma, derivation, candidate, provenance, and
advance-result values are also part of this interface because strategies must
construct and inspect them. Parsing, canonicalization, matching, substitution,
evaluation, derivation replay, evidence/request fingerprints, Lean rendering,
policy checks, and size enforcement remain implementation details behind those
few entry points and pure value operations.

`Admission` is one of `rejected`, `duplicate`, or `judge_request`. It includes a
stable reason/fingerprint and, only for `judge_request`, exact verdict/source
bytes. It never means accepted.

### Strategy registry

Interface:

```text
registered_strategies() -> tuple[Strategy, ...]
Strategy.open(problem) -> StrategySession
StrategySession.advance(EffortBudget) -> AdvanceResult
```

The stable registry initially contains one opaque countermodel portfolio and
four proof strategies: closed form, short chain, specialized synthesis, and
bidirectional rewriting. Portfolio stages, term-pool limits, table families,
frontiers, and all other tuning remain private session state. Registration is
the only enable/disable point used by paired benchmarks.

### Oracle subsystem

Interface:

```text
OracleSubsystem(mode, artifact_bytes).consult(
    problem, eq1_id, eq2_id
) -> OracleResult
```

Disabled mode structurally returns `disabled` without touching the artifact or
IDs. Enabled mode hides decoding, binding checks, cache indexes, shared magma
pools, direction data, and corruption handling. It may return one cached
candidate and one first-turn lane preference. A rejected or invalid cached
candidate clears that preference before reasoning starts.

### Case engine

Interface:

```text
run_case(start_message, judge_exchange, trace_recorder) -> CaseOutcome
```

This is the deep orchestration module. It derives the monotonic deadlines once,
parses the problem, consults the oracle once, admits and judges a cache candidate,
opens the stable strategy registry, grants hierarchical one-credit scheduler
turns, synchronously admits and judges yields, records dispositions, and stops
on acceptance, infrastructure error, exhaustion, or cutoff.

The deterministic scheduler remains inside this module. Splitting it into a
public scheduling interface would expose state that no other production caller
needs. Its pure transition functions can still be tested through internal seams.

`judge_exchange(verdict, source) -> JudgeResult` is a real seam with two
adapters: line-delimited stdin/stdout in production and an in-memory scripted
adapter in tests. `trace_recorder(record)` likewise has tagged-stderr and
in-memory adapters; only the case engine writes records. Benchmark tooling must
consume tagged stderr incrementally instead of relying on the proxy's bounded
final stderr tail. The recorder cannot be read by search code.

### Protocol adapter

The adapter owns JSON parsing/serialization and no solving decisions. It reads
the one startup object, constructs the case-engine inputs, and exchanges only
`judge` messages. `PROMPT` is the empty string and there is no LLM path.

The current executable proxy treats an accepted judge response as terminal and
does not implement a separate `submit` call. The adapter therefore exits after
`run_case`; an unsolved cutoff/exhaustion exits without fabricating a fallback
certificate. Startup limits are authoritative. A 300-second benchmark run uses
the versioned 30-second judge-start window and 2-second shutdown margin, but the
case engine derives its total deadline from the received timeout.

## Runtime ownership

```text
startup
  -> kernel.parse_problem
  -> oracle.consult
  -> [cached candidate -> kernel.admit -> judge_exchange]
  -> strategy_registry.open
  -> case engine chooses one session and grants one credit
  -> session.advance
  -> [candidate -> kernel.admit -> judge_exchange]
  -> repeat or stop
```

Only a judge `accepted` result produces a solved outcome. Cache rejection,
candidate rejection, strategy fault, and deadline crossing all return to or stop
the case engine according to the already resolved policies; none call back into
a strategy with feedback.

## Staged build sequence

Every stage leaves a runnable single-file artifact, reports its UTF-8 source
size, and runs the narrow tests before any benchmark. Later stages may not
change an earlier interface without first updating its contract tests and
deterministic trace fixtures.

1. **Lock the submission spine.** Add the empty `PROMPT`, startup decoder,
   monotonic profile derivation, stdout-only judge exchange, tagged-stderr trace
   recorder with incremental benchmark capture, and source/certificate byte
   guards. Prove with fixtures that an accepted judge response is terminal and
   that no `submit` or LLM call occurs.
2. **Build the kernel vertical slice.** Add canonical terms/problems, derivation
   factories, finite magmas, central admission, both renderers, fingerprints,
   and exact limits. Drive one structured TRUE fixture and one checked FALSE
   fixture through the real proxy/judge before adding search.
3. **Install the case engine with scripted sessions.** Port the accepted pure
   scheduler model, candidate disposition loop, deadline transitions, and
   observability projection. Scripted sessions exercise pause, yield, exhaust,
   fault, local rejection, judge rejection, acceptance, and cutoff. Remove the
   scripted registrations before the first coverage benchmark.
4. **Port the countermodel portfolio as one session.** Add exhaustive orders two
   and three, then structured orders four through seven, then seeded order-four
   backtracking. Validate pause/resume prefixes, exhaustive final magma checks,
   and deterministic table order. Run the FALSE-stratified development gate.
5. **Add proof strategies one at a time.** Promote closed forms, short chains,
   specialized synthesis, and bidirectional rewriting in that order. Each must
   yield a replayable derivation DAG, preserve deterministic prefixes, and pass
   its own oracle-disabled paired development comparison before the next one is
   enabled. Keep any controlled `lean_body` sweep provisional and separately
   registered.
6. **Prove composition, not just lane coverage.** Run repeated smoke cases and
   the 30/300-second paired development benchmark with both lanes enabled.
   Verify non-starvation, synchronous judge ordering, no baseline losses, trace
   projection stability, cutoff behavior, and section/source byte reports.
7. **Add the oracle disabled path before its data.** Implement both modes with an
   absent/corrupt/different artifact and prove disabled traces are identical.
   Then add content-bound cache and first-turn direction fixtures, including
   cache rejection clearing its hint. Reasoning registrations must remain
   byte-for-byte and behaviorally unchanged.
8. **Freeze the artifact and harden the single file.** Inventory only reusable
   accepted certificates, choose compression against the measured remaining
   source budget, embed the versioned bytes, and run enabled diagnostics plus
   oracle-disabled acceptance. Finish with the complete Solo harness, duplicate
   smoke runs, differing-case repeats, source/certificate size checks, and the
   full public-proxy comparison.

This order deliberately postpones corpus data and compression until the
reasoning engine exposes the artifact inventory and actual code footprint. It
also makes every strategy independently removable at the registry seam, which
is required for paired acceptance comparisons.

## Decision probes

The interactive prototype focuses on the highest-risk composition rules:

- disabled oracle mode never touches its artifact;
- cached evidence uses the ordinary admission and judge path;
- rejection or invalidity clears a cached direction hint;
- the first-turn hint is consumed when reasoning opens;
- local/judge rejection returns to unchanged search sessions;
- no candidate or judge work starts after the cutoff; and
- only judge acceptance solves a case.

The primary choice to react to is the physical source strategy: direct
single-file development now, with a generated bundler deferred unless the file
actually becomes a maintenance or size problem.
