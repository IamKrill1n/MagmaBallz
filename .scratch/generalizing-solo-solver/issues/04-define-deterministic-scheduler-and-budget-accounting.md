# Define deterministic scheduler and budget accounting

Status: resolved
Type: prototype
Blocked by: 02, 03, 05, 06, 07

## Question

How should the solver allocate reproducible work quotas across cheap stages,
countermodel search, proof search, certificate generation, and potentially slow
judge calls within an adjustable 300-second safety deadline, both with and
without a direction prediction?

## Comments

- Prototype evidence: [Deterministic scheduler prototype](../prototypes/scheduler_prototype.py), backed by its pure [scheduler state model](../prototypes/scheduler_model.py). It demonstrates lane-fair one-credit turns, proof-strategy rotation, first-slice-only direction preference, synchronous candidate admission/judging, and cutoff behavior. Awaiting the required HITL reaction before recording the answer and resolving this ticket.
- The human accepted the proposed scheduler and empirical judge-window guard on 2026-08-04.

## Answer

Use one deterministic, hierarchical credit scheduler. It grants a fixed one-credit
effort slice per scheduler turn, balances cumulative granted credits first between
the proof and countermodel lanes, and then balances credits among active strategy
sessions within the selected lane. Wall time never selects a strategy or changes a
slice size; it only prevents new work from starting at the versioned work cutoff.

### Startup and oracle path

The kernel parses and canonicalizes the problem, consults the oracle subsystem,
and processes a cached candidate before opening reasoning sessions. Cache evidence
uses zero search credits but follows normal admission and synchronous judging. If
it is not accepted, an invalid cache disables its associated hint as already
specified by the oracle contract; otherwise a usable direction hint is retained
for the first reasoning turn only.

Open all registered strategy sessions in stable registry order. The initial
registry contains the single opaque countermodel portfolio and the proof
strategies in their settled order: closed forms, short chains, specialized
synthesis, then bidirectional rewriting. A strategy's internal stages and tuning
remain invisible to the scheduler.

### Hierarchical fair scheduling

Each scheduler turn grants `EffortBudget(credits=1,
hard_deadline=work_cutoff)` to exactly one active session:

1. Choose the active lane with fewer cumulative granted credits.
2. On an equal-credit tie, alternate away from the lane selected most recently.
3. Within that lane, choose the active session with fewer cumulative granted
   credits, breaking ties by stable registry order.
4. Advance it once and synchronously process any yielded candidate before
   choosing another session.

For an unknown problem with no direction hint, the first tie is resolved in favor
of the countermodel lane, satisfying the required bounded countermodel-first
probe. A usable hint resolves only that first tie in favor of its predicted lane.
The ordinary credit rule applies afterward: the opposite lane catches up on the
next turn, so the hint reorders work without changing either lane's entitlement.

Count granted rather than used credits for fairness. A session that yields or
exhausts before consuming its whole grant cannot monopolize subsequent turns.
Record both values: granted credits describe scheduling entitlement, while used
credits describe completed deterministic work. Remove `exhausted` and `fault`
sessions from selection; a fault is recorded and does not stop other sessions.
Stop when every session is terminal or the work cutoff is reached.

The fixed one-credit sequence is deliberately independent of the wall-clock
budget. Subject to the same completed checkpoints and judge results, a shorter
profile therefore observes a prefix of the longer profile's grant sequence.
Do not add adaptive slice growth, measured-speed weighting, candidate-confidence
priorities, or per-strategy time quotas. A strategy version privately defines a
credit's deterministic work and checkpoint density; the public proxy benchmark
decides whether that version earns its cost.

### Candidate and judge accounting

A yielded candidate immediately enters the kernel-owned admission pipeline. Local
validation, evidence fingerprinting, rendering, policy checks, request
deduplication, and a permitted judge call complete before the next scheduler
turn. A local or judge rejection resumes ordinary fair scheduling; judge
acceptance terminates immediately; a judge infrastructure/configuration error
terminates the case run.

Keep four non-fungible ledgers instead of pretending unlike resources share one
exchange rate:

- per-session and per-lane search credits granted and used;
- deterministic kernel work counters, including candidate checks and rendered
  UTF-8 bytes;
- candidate, admission, deduplication, and disposition counts; and
- judge-call count and elapsed judge seconds.

Elapsed search, kernel, and judge times are diagnostics only. They never feed
back into strategy selection or credit grants. Candidate provenance retains the
originating session's cumulative used credits; case-run observability records
both cumulative granted and used totals at checkpoints.

### Deadline profile and cutoff behavior

Represent timing policy as a versioned budget profile containing the total
timeout, minimum judge-start window, shutdown margin, and fixed credits per turn.
For the initial 300-second profile:

```text
total timeout              = 300 seconds
minimum judge-start window = 30 seconds
shutdown margin            = 2 seconds
work cutoff                = 268 seconds after solver start
credits per turn           = 1
```

Derive all deadlines once from a monotonic clock when the solver receives the
start message. Do not start a strategy advancement, candidate admission, or judge
call at or beyond the work cutoff. Pass that same absolute cutoff to strategy
sessions so a deadline pause occurs only at deterministic safe checkpoints and
never reports exhaustion. If an advancement crosses the cutoff, retain its
credits-used accounting but do not begin processing a newly yielded candidate.
If admission crosses it, do not start the judge call. There is no unverified
fallback submission.

The 30-second judge window is an empirical start guard, not a guarantee that Lean
will return: the current Solo protocol does not let a solver impose a smaller
per-call timeout, and the proxy remains the authoritative hard-kill mechanism.
A judge call started before the cutoff may still consume the remaining process
budget and be killed. Preserve this outcome in observability rather than adapting
future turns from observed latency. Revisions to the window or margin create a
new budget-profile version; they do not change strategy behavior or credit order.

The accepted prototype is the [deterministic scheduler
prototype](../prototypes/scheduler_prototype.py), with its pure [scheduler state
model](../prototypes/scheduler_model.py) retained as planning evidence rather
than production code.
