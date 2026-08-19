# Define certificate validation and judge-call policy

Status: resolved
Type: grilling
Blocked by: 01

## Question

What local validation, Lean-source policy checks, candidate deduplication, and
judge-call rules should every generated proof or countermodel pass so that judge
latency is spent only on distinct, structurally credible certificates without
treating local checks as authoritative?

## Answer

Use one kernel-owned admission pipeline between strategy sessions and the judge.
It decides whether a candidate is locally admissible, but it never decides that
a certificate is correct. Only the judge's `accepted` response solves the
problem. Strategies receive no admission or judge feedback and simply continue
their deterministic candidate streams after a rejection.

### Admission sequence

For each candidate, the kernel:

1. checks the payload's basic type and shape and canonicalizes it without
   changing its meaning;
2. computes a problem-scoped evidence fingerprint and skips any disposition
   already recorded for that fingerprint;
3. performs the candidate-kind validation below;
4. renders the complete verdict-specific Lean source using the one canonical
   renderer;
5. scans that exact source for policy violations and enforces the advertised
   UTF-8 byte limits;
6. computes a problem-scoped request fingerprint from the verdict and exact
   rendered bytes, skipping any completed judge request with the same key; and
7. calls the judge synchronously if the global deadline guard still permits it.

Record rejected as well as admitted evidence fingerprints so duplicate invalid
candidates from another strategy do not repeat local work. Provenance is retained
for observability but has no effect on admission, deduplication, or ordering.

### Structured derivations

Do not trust a derivation merely because a strategy obtained a `Derivation`
value. Recursively replay its sealed `refl`, `hyp`, `symm`, `trans`, and `congr`
nodes in the kernel, rejecting cycles, foreign node tags, ill-scoped terms,
incomplete premise substitutions, endpoint mismatches, and malformed
compositions. Recompute every node's endpoints; the root must prove the
canonical goal in its required orientation.

Compute its fingerprint from rule tags, semantic node data, ordered
substitutions, and child fingerprints. Ignore object identities and whether
equal subproofs happen to be shared in memory. Do not attempt to identify
different proof trees that happen to prove the same equation.

### Countermodels

Require a positive order, exactly `n * n` row-major cells, and genuine integer
entries in `[0, n)`. Exhaustively evaluate the premise over every assignment and
then the goal over every assignment. The premise must hold universally, and the
goal must fail. Retain the lexicographically first failing goal assignment as
derived diagnostic evidence.

Fingerprint the order and exact row-major cells. Do not initially canonicalize
magmas up to carrier permutation: exact structural deduplication is simple and
sufficient until measurements show isomorphic duplicates consume meaningful
time.

### Controlled Lean bodies and rendered source

A `lean_body` is available only to the proof lane and remains provisional until
Lean accepts it. Normalize CRLF/CR line endings to LF and remove outer blank
lines; make no other edits. It must be a nonempty tactic body, not full source.
Reject imports, namespaces/sections, top-level commands or declarations,
submission scaffolding, judge-banned placeholder/unsafe/metaprogramming tokens,
and other known source-policy violations. Mirror the public judge's banned-token
scan, but do not add heuristic tactic bans such as rejecting automation merely
because it may be slow or unreliable.

The candidate gate never strips, repairs, or rewrites a body. A repair is a new
candidate from a separate deterministic strategy with its own provenance and
fingerprint. The renderer alone supplies fixed, branch-specific imports,
binders, `submission` declaration, countermodel helpers, indentation, and
escaping. Run the policy scan again on the complete rendered source and enforce
both the general code cap and the stricter false-certificate cap using exact
UTF-8 bytes. Do not run a second local Lean compiler: that would duplicate judge
latency without reproducing the authoritative dependency-policy check.

Fingerprint a Lean body from its normalized exact bytes. A second request-level
fingerprint over `(problem fingerprint, verdict, rendered source bytes)` catches
different evidence that converges to identical judge input. Do not normalize
internal whitespace, comments, or Lean syntax beyond the stated line-ending and
outer-blank-line rules.

### Judge-call ordering and deadline rule

Judge every distinct locally admissible candidate; there is no fixed call cap,
confidence threshold, per-strategy quota, or consecutive-rejection circuit
breaker. Validate, render, and judge synchronously before advancing another
strategy. Preserve the scheduler's deterministic yield order and never reorder
by candidate kind, provenance, or estimated likelihood of acceptance.

The budget profile supplies one global minimum judge window and a small shutdown
margin. Stop starting search work at the corresponding cutoff, and start a judge
call only while that minimum window remains. The window is benchmark-calibrated,
not adapted from timings observed during the current run and not exposed as a
strategy knob. It need not equal the judge's full 300-second timeout; requiring
that would leave no search time in the target budget. The deterministic
scheduler and benchmark decisions will choose and validate the concrete value.

### Judge responses

- `accepted` terminates the run immediately with the exact accepted verdict and
  rendered source.
- `incorrect`, `incomplete_proof`, `malformed`, and `unparsed` are recorded
  against the request fingerprint and are never retried. Continue advancing the
  unchanged strategy sessions while time remains.
- `malformed` or `unparsed` after local admission also records a kernel/renderer
  fault because the transport and schema are kernel-owned; it is not evidence
  against the originating strategy.
- A judge infrastructure or configuration `error` is not a candidate rejection.
  Stop issuing judge calls and terminate, because no local result can substitute
  for authoritative acceptance.

Expose these dispositions and timings to observability, but do not feed them
back into strategy behavior. Error-directed repair, if ever added, remains an
explicit deterministic strategy rather than a callback in the admission
pipeline.
