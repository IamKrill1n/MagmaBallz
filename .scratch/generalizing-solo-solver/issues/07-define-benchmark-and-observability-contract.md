# Define the benchmark and observability contract

Status: resolved
Type: grilling
Blocked by: none

## Question

Which public problem slices, TRUE/FALSE stratification, work and time
checkpoints, provenance fields, judge metrics, and reproducibility checks form
the acceptance contract for comparing each newly added strategy with the
cache-disabled baseline?

## Answer

Use a lightweight, versioned public proxy benchmark. The available public
problems contain equations of order at most four, while the held-back evaluation
includes order-five equations. Public gains therefore protect against
regressions and guide experiments; they are not evidence that a strategy will
generalize to the held-back distribution. Do not build a more elaborate
benchmark or tune individual problem pairs until representative data exists.

### Suites and comparison rule

- `sample_20` is the smoke suite. It checks startup, tracing, certificate flow,
  and both verdict branches, but does not gate strategy coverage.
- `hard1` plus `hard2` is the development benchmark: 269 cases, stratified as
  124 TRUE and 145 FALSE and also reported by source set.
- The acceptance benchmark is the 1,669 distinct labeled cases in `normal`,
  `hard1`, `hard2`, and `hard3`, stratified by source set and expected verdict.
  `sample_20` is already contained in `normal`; exclude the unlabeled
  `sample_200` from canonical comparisons.

Compare two fresh-process runs of the same source, budget profile, manifest,
environment, and strategy registry, with the new strategy disabled for the
baseline and enabled for the candidate. Disable both the certificate cache and
the direction predictor in both arms. Expected labels remain harness-only and
must never be passed to the solver.

Record results at 30 seconds and 300 seconds. The 30-second result is diagnostic.
At 300 seconds, a strategy passes development and then acceptance only if it adds
at least one judge-accepted case and loses none of the baseline's accepted cases
by exact problem ID. Report paired additions and losses; aggregate score alone is
insufficient. This rule is a public regression gate, not a claim about order-five
performance.

The initial 300-second budget profile reserves a 30-second minimum judge-start
window and a 2-second shutdown margin. These are versioned harness settings, not
strategy inputs. Judge timings are retained so a later profile can revise the
window without changing strategy behavior.

### Minimal observability contract

Keep observability kernel-owned and append-only. Strategies yield through their
existing interface and do not emit free-form telemetry or read benchmark state.
The recorder hides serialization and aggregation so tracing cannot affect search
ordering.

Each case run records:

- schema version; deterministic case-run ID; solver-source, configuration,
  manifest, and environment hashes; repeat index; problem ID and canonical
  fingerprint; source set and harness-only expected verdict;
- oracle mode and, when enabled, artifact version/digest; registered strategy IDs,
  versions, lanes, and private-configuration hashes;
- at each checkpoint, accepted state and verdict, accepting strategy and
  candidate kind, solve elapsed time, and cumulative credits granted and used by
  each strategy;
- candidates yielded, locally rejected by reason, evidence duplicates, locally
  admissible candidates, and duplicate rendered requests;
- judge-call index, originating candidate provenance, requested verdict, exact
  public status, elapsed time, and rendered UTF-8 byte count.

Candidate provenance remains the kernel-defined `strategy_id`,
`strategy_version`, `candidate_index`, `cumulative_credits`, and
`evidence_fingerprint`. Add candidate kind and the request fingerprint when
joining admission and judge records; do not add strategy-specific knobs.

The benchmark summary reports accepted coverage and paired additions/losses by
source set, expected TRUE/FALSE, strategy, and candidate kind. It also reports
candidate admission counts, judge status counts, total judge calls, total judge
seconds, and judge seconds per newly accepted case. Raw records remain available
for later analysis; no larger dashboard or percentile contract is required now.

Only the judge's `accepted` status counts as coverage. An `unparsed` or
`malformed` response after local admission is a kernel/transport fault and fails
the comparison. Judge infrastructure or configuration errors invalidate the
case run rather than counting as a strategy result. Other judge rejections are
diagnostic and remain governed by the no-fixed-call-cap policy.

### Reproducibility

- Manifests have stable ordering and content hashes; each problem runs in a
  fresh process. Do not combine resumed rows from different source,
  configuration, manifest, or environment hashes.
- For identical canonical input, strategy registry, private configurations, and
  granted-credit sequence, the ordered projection of strategy outcomes,
  candidate/evidence fingerprints, admission dispositions, rendered-request
  fingerprints, and judge statuses must be identical. Elapsed timings and the
  repeat index are excluded from this deterministic projection.
- Run the smoke suite twice. After a paired development or acceptance run,
  repeat every case whose 300-second accepted result differs between the two
  arms. The repeated final result and deterministic trace projection through
  each commonly completed effort slice must agree; otherwise the comparison is
  invalid.
- A hard deadline may truncate a deterministic stream only at a safe checkpoint.
  It may not reorder, skip, or falsely exhaust work. Timing-only movement across
  the 30-second checkpoint is reported but does not fail strategy acceptance.
