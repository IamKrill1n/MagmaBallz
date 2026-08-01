# Specify the oracle subsystem and disablement contract

Status: resolved
Type: grilling
Blocked by: 01

## Question

How should the optional direction predictor and artifact-backed certificate
cache be indexed, validated, toggled independently, and instrumented so that
known-corpus performance improves without contaminating the cache-disabled
generalization measurement?

## Answer

Use one deep, in-process oracle module with exactly two modes. In
`oracle-enabled` mode its certificate cache and corpus-derived direction
predictor operate together; in `oracle-disabled` mode neither is decoded or
consulted. Do not expose independent production toggles. A benchmark result may
be called a generalization measurement only when the mode is
`oracle-disabled`.

### Module seam and execution order

Configure the oracle once at process startup and consult it once, after the
kernel has parsed and canonicalized the problem but before the scheduler opens
strategy sessions:

```text
OracleSubsystem(mode, artifact_bytes)
  consult(problem, eq1_id, eq2_id) -> OracleResult

OracleResult
  cached_candidate : Candidate | none
  preferred_lane   : proof | countermodel | none
  disposition      : disabled | hit | miss | invalid
  artifact_ref     : diagnostic metadata | none
```

This is the only external seam. Artifact decoding, indexes, shared witness
pools, proof recipes, binding checks, and failure handling remain hidden in the
module. The kernel creates provenance for a cached candidate rather than
trusting provenance stored in the artifact.

The enabled path tries cached evidence first. If the judge accepts it, the case
is solved without starting reasoning. If there is no accepted cached candidate,
the scheduler may use `preferred_lane` for only its first bounded effort slice;
the ordinary deterministic fairness rules apply afterward. A direction hint
may not suppress the opposite lane, change its total entitlement, filter its
candidates, or act as a verdict.

An eulerv5-style quick proof or countermodel probe over the actual input is not
an oracle hint. It belongs in the reasoning engine as a deterministic strategy
and remains available in `oracle-disabled` mode.

### Identity and indexes

Use the ordered corpus pair `(eq1_id, eq2_id)` as the compact lookup key. The
numeric ordering of equation IDs has no logical meaning and must not be used to
infer implication direction. The official Equational Theories sources provide
no contract that the equation file is a topological ordering; see
[Equation-list order versus implication topology](../research/equation-order-topology.md).

IDs are indexes, not trusted semantic identity. The artifact contains a binding
table from every referenced equation ID to a 64-bit BLAKE2s tag of
`(canonicalization_version, canonical_equation_bytes)`. Both input equations
must match their tags before any pair entry is usable. A missing, out-of-range,
or mismatched binding cannot hit the cache or predictor.

Behind the seam, preserve dufius's reuse advantages:

- TRUE evidence is indexed by exact ordered pair and points to a structured
  derivation or controlled tactic-body recipe.
- FALSE evidence is a shared pool of finite magmas with their satisfied-equation
  ID sets, plus a per-premise index ordered by magma size and then stable
  artifact ordinal. A lookup chooses the first magma satisfying the premise and
  refuting the goal.
- Direction hints use an exact-pair bitset or sparse pair index, whichever the
  later size work selects. They yield only `proof`, `countermodel`, or no hint.

The logical indexes and ordering above are fixed; the byte-level compression
scheme remains an implementation choice because it depends on the final
artifact inventory and the 500 KB source cap.

### Artifact and candidate validation

The embedded artifact has a header containing a format version,
canonicalization version, producer/source-corpus digest, uncompressed length,
and payload digest. Decode lazily only in `oracle-enabled` mode. Before lookup,
verify the header, length, digest, binding-table shape, index bounds, unique pair
keys, and referenced artifact kinds.

Cache entries contain evidence, never a bare verdict or complete Lean
submission:

- countermodel entries reconstruct a `FiniteMagma`;
- proof entries reconstruct a sealed `Derivation` where possible;
- legacy deterministic proof recipes may reconstruct a controlled `lean_body`.

Every hit then follows the kernel-owned admission, deduplication, rendering,
policy, and synchronous judge-call pipeline defined by
`Define certificate validation and judge-call policy`. Use synthetic
kernel-generated provenance with strategy ID `oracle.cache`, artifact version as
the strategy version, stable entry ordinal as the candidate index, and zero
search credits. Only judge acceptance solves the problem.

A missing entry is an ordinary miss. A decode, schema, digest, binding, or local
candidate-validation failure makes the oracle invalid for the rest of the case
run and falls through to neutral oracle-disabled scheduling. A non-infrastructure
judge rejection of cached evidence does the same rather than continuing to use
its associated hint. Judge infrastructure/configuration errors retain the
kernel policy of terminating the case run. No oracle failure may trigger an
automatic re-enable, a partially trusted lookup, or a crash in the reasoning
engine.

### Disablement and contamination contract

`oracle-disabled` is a structural bypass, not merely "ignore cache hits":

- do not decode or validate artifact bytes;
- do not inspect pair IDs for oracle purposes;
- do not perform cache or predictor lookups;
- do not alter strategy registration, credit grants, first-lane choice, or
  candidate ordering based on artifact contents;
- emit only the fixed `disabled` consultation disposition.

The canonical strategy-development and acceptance comparisons defined by
`Define the benchmark and observability contract` run both arms in this mode.
Oracle-enabled versus oracle-disabled coverage may be reported separately as a
known-corpus performance diagnostic, never as evidence of generalization.

### Instrumentation

Extend each case run's kernel-owned trace with:

- oracle mode; artifact format/canonicalization versions and source/payload
  digests when enabled;
- consultation disposition and stable reason code;
- supplied pair IDs and per-equation binding result, without recording embedded
  payload bytes;
- cache evidence kind and stable artifact reference, or miss reason;
- predicted lane, whether it affected the first slice, and the eventual first
  lane actually scheduled;
- decode and lookup elapsed time as nondeterministic diagnostics;
- cached-candidate admission disposition, request fingerprint, judge status,
  and elapsed time through the existing candidate/judge records.

Include all fields except elapsed timings in the deterministic trace projection.
Strategies cannot emit, read, or branch on these records.

Regression coverage must prove that disabled mode never touches the artifact by
running with absent, corrupt, and deliberately different blobs and obtaining
the same ordered strategy/candidate trace. Also cover valid TRUE and FALSE hits,
ordinary misses, ID/text binding mismatches, unsupported versions, corrupt
digests and indexes, cached-candidate rejection, deterministic shared-magma
selection, and the rule that a hint affects at most the initial effort slice.
