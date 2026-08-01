# Wayfinder map: Generalizing zero-LLM Solo solver

Label: wayfinder:map

## Destination

An implementation-ready architecture and staged build plan for a deterministic,
zero-LLM Solo solver that maximizes verified certificate coverage on previously
uncached equation implications within an adjustable 300-second budget.

## Notes

- Use `SOLVER_ANALYSIS_NOTES.md` as the comparative source for existing solver
  mechanisms and defects.
- Use the `codebase-design` and `domain-modeling` skills when shaping interfaces
  and vocabulary; use `prototype` for empirical search-design questions.
- The first experiment disables the entire oracle subsystem. The architecture
  still includes an optional eulerv5-style direction predictor and a
  dufius-style artifact-backed certificate cache.
- Target Solo only: one problem per fresh process, one `solver.py`, at most
  500 KB. LLM calls and Marathon scheduling are excluded.
- Use a custom immutable magma-term representation shared by all strategies.
  Do not use SymPy in the first version.
- Search and scheduling must be reproducible. Unknown problems begin with a
  bounded countermodel-search slice, but neither proof nor countermodel search
  may be starved.
- This map plans the solver; it does not implement the completed solver.

## Decisions so far

<!-- Closed child tickets are indexed here. -->

- [Define the solver kernel and strategy interface](issues/01-define-solver-kernel-and-strategy-interface.md) — Use immutable canonical terms and deterministic resumable strategy sessions that yield centrally validated and rendered evidence under abstract credit slices.
- [Define certificate validation and judge-call policy](issues/05-define-certificate-validation-and-judge-call-policy.md) — Admit candidates through kind-specific checks and structural deduplication, then judge each distinct rendered certificate synchronously under one deadline guard while keeping acceptance authoritative.
- [Specify the oracle subsystem and disablement contract](issues/06-specify-oracle-subsystem-and-disablement-contract.md) — Use one ID-indexed, content-bound oracle module whose evidence cache and first-slice direction hint are jointly enabled or structurally bypassed, with all hits revalidated through the kernel.
- [Define the benchmark and observability contract](issues/07-define-benchmark-and-observability-contract.md) — Use lightweight oracle-disabled paired public-proxy runs at 30 and 300 seconds, with deterministic provenance and judge telemetry, while treating order-at-most-four coverage only as a regression signal.

## Not yet specified

- Whether the hard residual warrants equality saturation, derived-lemma
  synthesis, or another proof representation beyond bounded rewrite search
  depends on the measured coverage of the initial proof-search portfolio.
- The final compression scheme for oracle data depends on which reusable
  certificate artifacts the reasoning engine and benchmark expose.
- Exact source-flattening and size-reduction tactics for the one-file submission
  depend on the settled module interfaces and expected embedded data.
- Concrete implementation tickets and regression fixtures depend on the final
  architecture and build sequence.

## Out of scope

- LLM prompting, response repair, and LLM budget management.
- Marathon cross-problem scheduling or persistent caches.
- SymPy-backed reasoning in the first version.
- Pair-specific tuning against the held-back evaluation set.
- Treating public order-at-most-four benchmark gains as evidence of
  generalization to held-back order-five equations.
- Implementing the completed solver during this planning effort.
