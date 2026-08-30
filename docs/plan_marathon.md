 # Marathon Adaptation Plan — My Supreme Leader’s Solver

  > Target file: docs/marathon_plan.md

  ## Summary

  Adapt my_submission/solver.py into a dual-mode solver:

  - Preserve the existing Solo stdin/stdout behavior.
  - Detect Marathon through JUDGE_MARATHON_MANIFEST.
  - Use coverage-first triage, resumable solving phases, validated knowledge
    reuse, and bounded concurrency.

  - Keep the final single-file submission below 500,000 bytes

  - Do not change runner, proxy, judge, or scoring contracts.

  ## Implementation Changes

  ### 1. Recover source space and add mode adapters

  - Keep PROMPT as a top-level string literal because the Solo proxy extracts
    it statically.

  - Compress other large prompt fragments, strategy cards, advice, and
    protocol messages into an embedded zlib/base85 string table.

  - Remove unreachable wrappers and aliases. If more space is required, prune
    largest routes with zero unique benchmark wins, while retaining all core
    finite search, midpoint, superposition, completion, and infinite-model
    capabilities.

  - Change main() to select:
      - Solo adapter when Marathon environment variables are absent.
      - Marathon batch driver when they are present.

  - Introduce an internal execution context so existing solver code calls
    abstract judge and LLM adapters:
      - Solo adapters retain the current JSON protocol.
      - Marathon LLM adapter renders PROMPT locally and calls
        marathon_llm.call_llm.

      - Marathon judge adapter locally validates certificates and returns the
        same status shape expected by current feedback logic.

  ### 2. Make solving resumable

  Replace monolithic solve() orchestration with a serializable ProblemState
  containing parsed equations, semantic classification, current phase,
  candidate blackboard, judge feedback, failed routes, progress signals,
  resource usage, and validated examples.

  Run each problem through these phases:

  1. Preflight/cache — parse, classify, try embedded certificates.
  2. Cheap — no LLM; small countermodels, rigidity scout, and shallow focused
     proofs. Cap: 8 seconds per problem.

  3. Focused — standard auxiliary proofs, grounding, helper chains, moderate
     finite search, and at most one low-effort 4,096-token LLM call. Cap: 60
     seconds.

  4. Deep — larger countermodel portfolio, saturation/completion, and at most
     one medium-effort 8,192-token LLM call. Cap: 180 seconds.

  5. Recovery — only high-progress unresolved problems; one final high-effort
     call with at most 16,384 output tokens. Cap: 90 seconds.

  Solo mode runs the same phases consecutively, preserving the existing route
  order and effective per-problem behavior.

  ### 3. Add the global Marathon scheduler

  - Divide usable wall time into 15% cheap, 50% focused, 25% deep, and 10%
    recovery pools. Roll unused time forward.

  - Divide LLM tokens into 70% focused, 20% deep, and 10% recovery pools.
  - Preserve a 15–60 second shutdown margin: min(60, max(15, 1% of global wall
    budget)).

  - Process every cheap phase before spending LLM tokens.
  - Rank later work deterministically by:
      1. Focused structural matcher available.
      2. Similarity to validated examples.
      3. Mechanical progress already observed.
      4. Smaller equation size and variable count.
      5. Problem ID as stable tie-breaker.

  - Use two isolated problem worker processes. This preserves process-local
    signals and prevents shared feedback corruption.

  - Permit only one in-flight LLM call and one Lean validation globally
    through cross-process semaphores.

  - Enforce phase deadlines from the parent; terminate overdue workers and
    requeue their last completed state when useful.

  - Maintain a conservative shared token ledger. Charge successful calls by
    reported usage and failed upstream calls by their pessimistic reservation;
    treat HTTP 402 as closure of the LLM lane.

  ### 4. Validate, emit, and reuse safely

  - Validate every certificate selected for output or reuse:
      - Generate the per-problem JudgeProblem module in Marathon scratch.
      - Compile the full candidate with lake env lean.
      - Run the dependency report and enforce the problem’s proof policy.
      - Fail closed when Lean tooling is unavailable or validation times out.

  - Keep one parent-owned JSONL writer. Append, flush, and fsync each
    validated answer immediately.

  - Never replace an already validated answer for the same problem.
  - Admit only validated true proofs into the cross-problem example pool.
  - Select at most two structurally similar examples per prompt, capped at
    6,000 total characters.

  - Treat cross-problem proofs as prompt examples only; never import their
    lemmas mechanically unless the hypothesis signature is identical.

  - Cache finite models and proof artifacts only within the current run’s
    scratch directory.

  ## Test Plan

  - Capture the current Solo sample results and route winners before
    refactoring.
      - Solo/Marathon mode selection.
      - Prompt rendering parity with the Solo proxy.
      - ProblemState serialization and phase resumption.
      - Deterministic ranking and budget roll-forward.
      - Two-worker, one-LLM, and one-Lean concurrency limits.
      - Worker timeout and clean requeue behavior.
      - Token exhaustion, zero-token mode, and failed-call charging.
      - Local acceptance of known true/false certificates.
      - Rejection of malformed, forbidden, or policy-violating certificates.
      - Single-writer JSONL integrity and immediate persistence.
      - Validated-only few-shot admission and prompt-size limits.

  - Required gates:
      - python3 -m py_compile my_submission/solver.py
      - Source size strictly below 500,000 bytes; target ≤485,000.
      - python3 scripts/run_harness.py
      - python3 scripts/run_marathon_harness.py
      - Solo sample_20 accepted set must not regress from the captured
        baseline.

      - Marathon normal_5 with zero LLM tokens must score at least the bundled
        brute-force baseline.

      - Run normal_100 at compression ratio 0.5 with one and two workers; two-
        worker mode must not reduce score and should reduce wall time.

      - Validate the final output contains no duplicate IDs or rejected
        certificates.

  ## Assumptions

  - The documented Marathon environment exposes Lean tooling and judge
    libraries inside the sandbox.

  - Production reference resources remain 2 CPUs, 2 GB memory, and 64
    processes.

  - Linux process isolation is available; workers remain descendants of the
    single solver process and inside its sandbox.

  - Deterministic seeds and stable problem-ID tie-breaking remain mandatory.
  - No new public environment variables or submission files are introduced.