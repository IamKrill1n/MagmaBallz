# MagmaBallz

MagmaBallz evaluates certificate-producing solvers for implication between
equational laws over finite or arbitrary magmas.

## Language

**Generalization**:
The ability of a solver's reasoning machinery to produce verified certificates
for equation implications while the oracle subsystem is disabled.
_Avoid_: Oracle coverage, corpus recall

**Public proxy benchmark**:
A fixed public order-at-most-four problem corpus run with the oracle subsystem
disabled to compare reasoning-engine versions. Its results do not establish
generalization to held-back order-five equations.
_Avoid_: Generalization benchmark, held-back evaluation

**Development benchmark**:
The public `hard1` and `hard2` problem sets used for routine paired strategy
comparisons before the full public acceptance benchmark is run.
_Avoid_: Smoke benchmark, acceptance benchmark

**Acceptance benchmark**:
The complete labeled public `normal`, `hard1`, `hard2`, and `hard3` corpus used
for the final public-proxy comparison of a solver change with its oracle-disabled
baseline.
_Avoid_: Development benchmark, held-back evaluation, generalization evidence

**Strategy acceptance**:
A paired comparison in which enabling a strategy gains at least one
judge-accepted case and loses none of the baseline's accepted cases at the final
budget checkpoint.
_Avoid_: Aggregate score increase, unpaired benchmark result

**Case run**:
One reproducibly identified execution of a solver configuration on one canonical
problem within a benchmark.
_Avoid_: Wall-clock invocation, unversioned result

**Certificate cache**:
An optional store of known problem-pair candidate evidence that can answer
before reasoning begins after normal validation and judge acceptance.
_Avoid_: Oracle, reasoning engine

**Direction predictor**:
An optional corpus-derived estimate of whether proof search or countermodel
search should receive the first bounded search slice. It schedules work but
never constitutes a certificate; search-derived probes belong to the reasoning
engine instead.
_Avoid_: Certificate cache, verdict

**Oracle subsystem**:
The optional combination of the certificate cache and direction predictor for
known equation pairs. Its two parts are enabled or disabled together.
_Avoid_: Reasoning engine

**Oracle mode**:
The per-process choice between enabling the whole oracle subsystem and
structurally bypassing it. Generalization is measured only in the disabled mode.
_Avoid_: Cache-only mode, predictor-only mode

**Reasoning engine**:
The certificate-producing machinery used when the oracle subsystem is disabled
or its certificate cache misses.
_Avoid_: Certificate cache

**Solo solver**:
A certificate-producing submission that handles one implication problem in a
fresh process under an independent wall-clock budget.
_Avoid_: Marathon scheduler, persistent agent

**Strategy session**:
The opaque, resumable state of one deterministic proof or countermodel search
for one problem. The scheduler advances it with generic effort slices without
knowing the search's internal tuning parameters.
_Avoid_: One-shot strategy call, scheduler-owned search state

**Countermodel portfolio**:
The deterministic countermodel strategy that coordinates complementary
finite-magma searches and their bounded shared search knowledge.
_Avoid_: Random table search, scheduler-managed search stages

**Premise-model**:
A finite magma that satisfies a problem's premise, whether or not it falsifies
the goal. It is a countermodel only when it also falsifies the goal.
_Avoid_: Countermodel, witness

**Effort slice**:
A reproducible allowance of abstract work credits granted to a strategy session,
paired with a hard deadline used only to prevent overruns.
_Avoid_: Strategy-specific depth limit, primary wall-clock budget

**Search lane**:
The proof or countermodel class across which the scheduler balances cumulative
credit entitlement before choosing an individual strategy session.
_Avoid_: Verdict prediction, strategy stage

**Scheduler turn**:
One deterministic grant of a fixed effort slice to one active strategy session,
followed by synchronous processing of any candidate it yields.
_Avoid_: Time slice, strategy round

**Budget profile**:
A versioned per-case timing policy containing the total timeout, minimum
judge-start window, shutdown margin, and credits granted per scheduler turn.
_Avoid_: Adaptive time allocation, strategy budget

**Work cutoff**:
The budget-profile instant after which a case run begins no new strategy,
candidate-admission, or judge work so the judge window and shutdown margin remain.
_Avoid_: Strategy timeout, proof deadline

**Deterministic strategy**:
A search whose ordered candidate stream is fixed by the canonical problem,
strategy version, and granted effort credits. It uses no random sampling, and a
hard deadline may pause but never reorder or skip its work.
_Avoid_: Seeded random strategy, wall-clock-directed search

**Candidate**:
Proof or countermodel evidence yielded by a strategy for central validation and
Lean verification. A candidate is not a solved problem until the judge accepts
its rendered certificate.
_Avoid_: Solution, accepted verdict

**Locally admissible candidate**:
A distinct candidate that passes the kernel's objective, type-specific checks
and is therefore worth a judge call. Local admissibility never establishes that
the certificate is correct.
_Avoid_: Valid certificate, locally verified solution

**Evidence fingerprint**:
A deterministic identity derived from a candidate's kind and canonical payload,
excluding provenance and in-memory sharing layout. It supports structural
deduplication without claiming mathematical equivalence.
_Avoid_: Proof equivalence, provenance hash
