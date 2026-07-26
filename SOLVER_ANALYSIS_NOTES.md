# Solo demo solver analysis — session notes

Session of 2026-07-26. Captured to disk because the session transcript was not
being persisted (inherited `CLAUDE_CODE_CHILD_SESSION` marker).

Scope: `examples/solo/demos/` — 11 files, 8 directories.

---

## 1. Duplication map (verified by `diff` / function-set comparison)

| File | Status |
|---|---|
| `emily/EQT02-S00011.py` | Exact duplicate of `S00012.py` apart from one leading blank line |
| `emily/EQT02-S00019.py` | 40-line retune of `opnorm/solver.py`; identical 77-function inventory |
| `twophase/solver.py` | Superseded by `opnorm` (same 75 functions + 2) |
| `dufius/EQT02-S00005.py` | Superseded by `S00007` (42 of 49 functions byte-identical) |

Distinct solvers: **opnorm, eulerv5, dufius/S00007, suii0x, baseline, owen**
(+ `emily/S00012` as a small variant).

---

## 2. Per-solver summary

### opnorm (4667 L) — repair-centric reference solver
Single-phase "MATCH-COLLAPSE" LLM prompt over ~11 reachable deterministic routes:
3 counterexample tiers (exhaustive Fin<=3 -> structured/product families Fin 2-7 +
5k random -> backtracking Fin 4-5, 10 s), then singleton -> direct substitution ->
calc-chain BFS -> compound calc -> constancy -> hybrid -> deep-constancy ->
simp-rewrite -> bidirectional subexpression BFS (120k states, 30 s).

Distinctive machinery is the repair layer:
- `preflight_proof` — local tactic banlist before spending a judge call
- `try_symm_repair` — flip `.symm`, resubmit
- `extract_calc_intermediates` — seeds a bounded BFS rerun from a rejected LLM proof
- `parse_lean_error` -> `build_fix_hint` — typed judge stderr into a natural-language directive

Temps `[0.3, 0.5, 0.7, 0.9]`. Round loop unbounded (harness enforces wall clock).

Caveats found: ~1,100 lines of `try_*` strategies defined but never called from
`main()`; two library-lookup routes permanently stubbed to `False`; several JSON
side-tables referenced by path but not shipped. The docstring's "16 strategies"
overstates what actually executes.

### eulerv5 (3177 L) — ships the answer key
`_MATRIX_BLOB` decompresses to exactly 2,754,205 bytes = 4694^2 bits
(`_MATRIX_N = 4694`) — an O(1) oracle for every ordered pair of the 4,694 known
Equational Theories Project equations. Verified by decompressing it.
Backed by 390 machine-verified proofs (`_AB`, 90,240 bytes) and 238 verified
counterexample tables.

Everything else — bidirectional meet-in-the-middle rewrite BFS with `CONST`/`LCONST`
transitions, five zero-LLM specialized engines, a 50-candidate tactic sweep,
invertibility patterns from Tao's Lean files, an LLM tier — exists only for the
out-of-corpus residual. Hence the direction predictor (2 s counterexample probe +
`find_proof` probe) before choosing an attack.

Budget-aware: `llm_reserve = min(30, 0.3*budget)`, round count = `budget/45`.
Only demo with Marathon support, though it gates on `JUDGE_MARATHON_MANIFEST`
alone, not the documented two-var pair.

Tactic heuristics reverse-engineered from an external proof corpus — comments cite
frequency stats ("compound terms... 71% of successful instantiations").

### dufius/S00007 (3758 L) — data + unification, judge-call economics
Organizing principle: **judge calls are the scarce resource** (comment at line 3688
puts a rejection at ~5 min of Lean compile).

Cascade:
- **Layer 0** `_oracle_verdict` — routing signal only
- **Layer 0b** bundled witness (oracle FALSE) — re-verified locally, 1 judge call
- **Layer 0c** `_try_auto_proof` — unification, 1-step + four 2-step chain shapes
- **Layer 0d** SimpleRewrites lookup (oracle TRUE)
- **Layer 1** rule engine: X1 reflexive; S1/S2 leftmost/rightmost-leaf projection;
  S4 XOR parity; affine library M1-M9
- **Layer 1.5** brute force — exhaustive Fin 2 (16) and Fin 3 (19,683), structured
  families only at Fin 4-5. Budget 20 s if oracle silent, 120 s if oracle said FALSE.
  Skipped entirely if oracle said TRUE.
- **Layer 3** LLM, <=8 rounds

Oracle design (better than a raw truth table): `_oracle_verdict` never reads a
stored verdict, it infers — a bundled magma satisfying Eq1 and not Eq2 => FALSE
(and you hold the proof); a SimpleRewrites recipe exists => TRUE (ditto); neither
=> unknown. Both directions backed by a constructive artifact, re-verified locally.
Storage is compact because the DB stores 1,683 magmas each with its *set* of
satisfied equations, indexed per-equation smallest-first — one magma covers every
pair it separates.

The third branch does the real work: "no witness in our DB" is treated as evidence
of TRUE, driving the short brute-force budget, the prompt's `DEFAULT TO TRUE` block,
and the explanation given to the model.

LLM circuit breakers: `MAX_CONSECUTIVE_UNVERIFIED = 3`, `MAX_JUDGE_REJECTIONS = 2`
(cited evidence: "gpt-oss-120b that fails the first two cert attempts effectively
never recovers later"), plus an oracle-disagreement guard that discards
contradicting verdicts without a judge call. Rejected tables accumulate and the
last 5 are fed back as a do-not-repeat list.

Brittleness found:
- Oracle-suppression guard is applied at Layers 1 and 3 but **not** at 0c
- `emit_singleton_certificate` requires `lhs1 == "x"` literally (line 3193)
- `try_x3`'s second branch returns a `RuleResult` with no certificate and is inert
- Fin 4-5 not exhaustive; sporadic counterexamples there are invisible
- `solve_problem` (line 3462) is dead code — never called
- No Lean sanitization: no size cap, no import allowlist, no `sorry`/`axiom` scan
- Marathon dropped, not moved — `run_marathon` from S00005 has no trace

### suii0x (922 L) — zero LLM by construction
`PROMPT = ""`, no `call_llm` anywhere. 20 s structured counterexample search
(exhaustive Fin 2-3, then constant/projection/min-max/affine-grid/band/product/
projection-exception families to Fin 7), then 7 closed-form TRUE synthesizers built
around a 64-entry term pool: singleton, direct substitution (var-only and compound),
1-2 hop calc chains, one-`congrArg` bridging, constancy.

Nothing deeper than 2 hops or one congruence. Vestigial `<think>`-tag stripping
suggests an LLM path was removed. Ends with a deliberate doomed `exact h` canary so
a run is never zero-judge-call.

No shared ancestor with dufius — zero function-name overlap, unrelated naming
conventions. Convergence is from the framework contract, not lineage.

### baseline (294 L)
Brute force Fin<=3 -> singleton-collapse pattern -> unbounded LLM loop, on the
documented stdio protocol, relying on the proxy's `{history.*}` injection.

### owen (152 L)
Pure LLM passthrough, 8 fixed rounds, no deterministic reasoning. Tightest feedback
discipline of the small solvers. **Uses an HTTP session REST API**
(`PIPELINE_API_BASE`, verified via `urllib` import), not the stdio contract.

### emily/S00012 (180 L)
owen's HTTP scaffolding with the LLM stage deleted and baseline's table-enumeration
algorithm ported in (same bit-packing formula, renamed variables; extended to a
120k-sample Fin 4 tier). Structurally can only ever answer FALSE.

---

## 3. Cross-cutting observations

**Three mutually exclusive strategic bets:**
- *Precompute* (eulerv5, dufius) — ship verified answers/witnesses as compressed
  data, reserve reasoning for the residual. Depends on the judge's ID numbering
  matching the mined corpus.
- *Search* (suii0x, emily/S00019) — spend CPU on finite countermodels so a verified
  Fin table replaces uncertain proof attempts. S00019's entire 40-line diff is this:
  `max_n` 5->6, random 5k->16k, backtracking `(4,5)`->`(4,5,6)` at 10 s->22 s, and
  colder temps `[0.12...0.85]` because after an aggressive search the LLM should be
  literal, not creative.
- *Repair* (opnorm, twophase) — assume the LLM lands close, invest in typed error
  parsing, `.symm` toggling, BFS completion of near-miss proofs.

**Nobody sanitizes Lean.** None of the demos has `sanitize_lean_code`, an import
allowlist, or byte-size caps. Local gates are semantic (table satisfies Eq1, refutes
Eq2 — every solver does check this before a judge call) plus regex tactic banlists.
`EQT02-M00006.py` is the only file in the repo implementing the documented contract.

**Nobody caches term operations.** No `@lru_cache` in any demo. opnorm and eulerv5
each maintain two parallel term representations with duplicated parsing logic.

**Convergent design.** Independently authored solvers landed on the same shapes:
singleton-collapse detection, affine `(ai+bj+c) mod n` families, `finOpTable` +
`decideFin!` FALSE certificates, local table verification before judging. The last
three are forced by `judge/verify.py`'s support modules; the first two are genuine
independent discovery.

---

## 4. FINDING: `_try_auto_proof`'s plain `trans` row has its link pair swapped

**File:** `examples/solo/demos/dufius/EQT02-S00007.py`, line ~2952
**Status:** verified empirically, not yet filed as an issue

### The mechanism

A two-hop chain `(h sigma).trans (h tau)` imposes three constraints:

1. `sigma(L1) = L2` — left end
2. `tau(R1) = R2` — right end
3. `sigma(R1) = tau(L1)` — the joint (this shared expression is M)

Constraints 1 and 2 are matching problems solved against the goal's two ends.
Constraint 3 has no unknowns left, so it is a structural-equality *check*, not a
solve. M is never searched for — each half computes a candidate midpoint and the
check asks whether they agree.

### The four orientations

Rule: whichever side of the assumption matches the goal, the *other* side is the
midpoint end.

| # | Shape | sigma from | tau from | correct joint |
|---|---|---|---|---|
| 1 | `(h s).trans (h t)` | L1~L2 | R1~R2 | `s(R1) = t(L1)` |
| 2 | `(h s).trans (h t).symm` | L1~L2 | L1~R2 | `s(R1) = t(R1)` |
| 3 | `(h s).symm.trans (h t)` | R1~L2 | R1~R2 | `s(L1) = t(L1)` |
| 4 | `(h s).symm.trans (h t).symm` | R1~L2 | L1~R2 | `s(L1) = t(R1)` |

Rows 2, 3 and 4 are wired correctly. **Row 1's link pair is written as `(L1, R1)`,
which yields `s(L1)` vs `t(R1)` — row 4's condition.** By construction those are
just `L2` and `R2`, so the check tests whether the goal's own two sides are
identical. It should be `(R1, L1)`.

### Repro

```python
# assumption: x * y = (y * x) * y
# goal:       a * b = (b * (b * a)) * b
# valid proof: (h a b).trans (h (b*a) b)
sigma(R1) = ((b*a)*b)
tau(L1)   = ((b*a)*b)
  joint sigma(R1)==tau(L1)?          True     <- the chain is valid
  what the code actually compares?   False    <- wrong pair
_try_auto_proof -> None
```

With only that row's pair swapped to `(R1, L1)`:

```
_try_auto_proof -> ('intro a b\n  exact (h a b).trans (h (b*a) b)', '2_trans')
```

### Impact

The most natural two-hop shape — no `.symm` anywhere — never fires. Everything
reaching it falls through to brute force and then the LLM.

Second-order: when the goal is reflexive, the broken check *passes* and a
certificate is emitted without the real joint ever being verified — likely
ill-typed, costing a judge call. The X1 rule that properly handles reflexive goals
sits at Layer 1, which runs *after* this detector.

### A limitation that survives the fix

Matching `L1` against `L2` only binds variables occurring in `L1`. If the assumption
has a variable appearing only on its right side, sigma leaves it unbound and
`sigma(R1)` still contains a loose variable — at which point the joint is an
equation to *solve*, not an identity to check. Verified:

```python
# assumption: x = y * x ,  goal: a = c * (b * a)
# valid chain exists: (h a b).trans (h (b*a) c)
sigma = {x: a}          # y never bound
sigma(R1) = (y*a)       tau(L1) = (b*a)
-> None   (even on the link-corrected build)
```

Concrete improvement: at the joint, *match* `sigma(R1)` against `tau(L1)` instead of
testing equality. Then `y` binds to `b` and the chain goes through.

Other limits, not fixable within this design: depth capped at two; both matches are
against the whole side, so rewrites inside a subexpression are invisible
(`match(x*x, (a*a)*b) = None`, verified); no derived lemmas; matching is exact with
no normalization.

### Next step

Per `CONTRIBUTING.md` this is a substantive correctness change and needs a filed
issue before a PR. Issues live under `.scratch/<feature>/`.

---

## 5. eulerv5 BFS: near-misses, expression comparison, and closure

### The BFS itself (`proof_bfs_v5`, ~line 1928)

Bidirectional. A forward frontier grows from the goal's LEFT side, a backward
frontier from the goal's RIGHT side, applying instantiated hypothesis rewrites at
any subterm position (`gen()` recurses into `("op", l, r)` at path `"L"`/`"R"`).

Bookkeeping:

```python
fwd = {start: None}   # norm -> (prev_norm, path, args, symm, prev_tree, this_tree)
bwd = {target: None}
state_cap = max(20000, min(500000, int(time_limit * 8000)))
```

Generated terms are capped at `_tsize5(...) <= 20` nodes.

Two extra rewrite kinds beyond plain `h` / `h.symm`: `CONST` and `LCONST`, which
exploit variables free on only one side of the hypothesis to jump between
differently-instantiated but semantically linked subterms.

**Success = collision.** `if nn in bwd` — exact identity of canonical strings. At
that point the forward path proves `left = M`, the backward path proves
`M = right`, and the recorded paths reconstruct a `calc` chain (each step wrapped
via `_wrap5` according to the rewrite path).

### What a "near-miss" is

If the frontiers never collide the search fails, but up to 500k expressions were
explored. The failure path harvests some of them (line ~2149):

```python
for nn in fwd:
    if nn in bwd: continue
    overlap = sum(1 for c in nn if c in target)
    if overlap > len(target) * 0.5:
        _last_bfs_near_misses.append((nn, overlap, total_states))
_last_bfs_near_misses.sort(key=lambda x: -x[1])
_last_bfs_near_misses = _last_bfs_near_misses[:5]
```

A near-miss is an expression the FORWARD search actually reached — so a proof that
`goal_left = E` already exists (replay the recorded rewrites) — but which never
linked up to the backward frontier.

**Purpose:** `_build_llm_hints` (line ~1499) injects the top 3 into the LLM prompt,
but only when the oracle says the verdict is TRUE:

```
BFS NEAR-MISS RESULTS (use these!):
  Near-miss: <expression> (overlap: N)
  BFS explored <N> states.
  The gap between the nearest expression and the goal
  is a bounded sub-problem. Close it with constancy or congr_arg.
```

This is the strongest idea in eulerv5's design: a failed deterministic search hands
the model a *partial result*, converting total failure into a reduced problem, and
the state count tells the model the cheap paths are already exhausted.

Sibling mechanism: `_last_tactic_failures` injects the tactic sweep's failures as
"TACTIC SWEEP ALREADY TRIED (do NOT re-propose these)" with Lean's actual errors.

### FINDING: the near-miss score does not measure similarity

`sum(1 for c in nn if c in target)` counts, per character of the candidate, whether
that character occurs ANYWHERE in the target. The alphabet is only variable letters,
the operator, and parentheses — so almost every candidate scores its own full
length. Verified:

```
'(x-y)-x'              len= 7  overlap= 7
'(y-x)-y'              len= 7  overlap= 7
'((x-x)-(y-y))-(x-y)'  len=19  overlap=19
```

Two structurally unrelated expressions of equal length score identically, and a
large unrelated expression outscores an exact structural neighbour. Since the list
sorts by overlap descending, **the ranking is effectively longest-first** — and the
longest states are the deepest, most-rewritten ones, i.e. the least likely to be
near the goal. The `> len(target) * 0.5` threshold is likewise a length filter.

Two available improvements, both already in the file or the data structure:
- `_string_overlap5` (line 2341) computes a longest-common-substring score and does
  measure shared structure. It ranks `rw` chains but is not used here.
- Depth-in-the-search is a better proxy for "close" than length. It is recoverable
  by walking `prev_norm` back to `start`, and the expansion loop
  (`for depth in range(max_depth)`) knows it while building — but it is neither
  stored per state nor used for ranking.

Impact is bounded: near-miss scores never affect correctness, only which hint the
model sees. Term size is also capped at 20 nodes, so the length bias has a ceiling.

### How expressions get compared (two distinct mechanisms)

**Exact — affects correctness.** Every expression is rendered to a canonical string
by `_tnorm5`; those strings are the dict keys. "Same expression" means identical
canonical string, i.e. structural tree equality by proxy. Used for the collision
test and for dedup. Matching is the other exact comparison: directional, all-or-
nothing. Proofs are only ever built on exact agreement.

**Heuristic — affects ranking only.** `_string_overlap5` and the near-miss counter.
A bad similarity score can waste an attempt or produce an unhelpful hint; it can
never produce a wrong certificate, because anything that becomes a certificate still
passes exact matching and then the judge. This is why the sloppiness is tolerable
here in a way it would not be in the collision test.

### When is something "closed"?

Three gates, only the last authoritative:

1. **In the search** — collision (`nn in bwd`), exact.
2. **Before submitting** — `preflight_v5` rejects `sorry`/`admit`, the banned
   automation list (`aesop, omega, norm_num, ring, field_simp, decide, tauto,
   linarith, positivity, polyrith, nlinarith`), bare `simp` without `only`,
   underscore-typed `have`, and references to the nonexistent
   `equational_theories` library. FALSE tables are checked against both equations
   by `check_equation`. These are filters against WASTING a judge call, not
   judgments of correctness.
3. **The judge** — compiles and returns one of the five statuses. No solver decides
   a proof is correct; it only decides a candidate is worth a compile. The Lean
   kernel decides closure. Same reason a counterexample table is a certificate
   rather than a claim: the judge recomputes both laws over every assignment.

**Closed in the term sense** (no free variables) is a separate and load-bearing
notion. A substitution yields a closed expression only if every variable was bound.
This is precisely the dufius limitation in section 4: when sigma is solved from one
side and a variable occurs only on the other, `sigma(R1)` retains a loose variable
and structural equality against a closed expression fails. Closedness is the
precondition for the joint check to be meaningful. eulerv5's `CONST`/`LCONST`
transitions go the other way — they deliberately exploit one-sided free variables to
generate additional rewrites.

---

## 6. eulerv5 BFS: the graph model, and what the search is actually for

### Nodes are expressions, not equations

```python
start, target = _tnorm5(glt), _tnorm5(grt)   # goal's LEFT tree, goal's RIGHT tree
fwd = {start: None}
bwd = {target: None}
```

- **node** = a single expression (keyed by its canonical string from `_tnorm5`)
- **edge** = one application of the hypothesis at one subterm position, carrying its
  justification (`h args`, `(h args).symm`, or a `CONST|…`/`LCONST|…` step)
- **path from A to B** = a proof that `A = B`

The equation is not a node — it is the *pair of endpoints*, and the proof is the
route between them. "Does `L2 = R2` hold" becomes "are these two nodes connected,
and can you exhibit a path." Provable equality is graph connectivity.

`L1 = R1` is therefore not an edge but the **edge generator**: every (instantiation
x position x direction) triple is a different edge. Edges are effectively
undirected, since `.symm` supplies the reverse (the `symm` flag rides in the stored
tuple and `_wrap5` inserts `.symm` on reconstruction).

Because the search is for a *connection between two known nodes* rather than for a
node with some property, bidirectional search is the natural shape: two balls of
radius d/2 beat one ball of radius d, and the branching factor here is severe.

### What it searches for: a frontier collision

Not a proof, and not the goal — a single expression present in **both** frontiers.
The code says it directly:

```python
fwd[nn] = (nm, path, args, symm, t, nt)
total_states += 1

# Check: does this meet the backward frontier?
if nn in bwd:
```

The backward-expansion loop mirrors it with `if nn in fwd`. On collision:

```python
fwd_chain, cur = [], nn
while fwd[cur] is not None:
    fwd_chain.append(fwd[cur]); cur = fwd[cur][0]
fwd_chain.reverse()
# ... same walk on bwd ...
bwd_chain_flipped = [(prev, p, a, not s, prev_t, this_t) for ... in bwd_chain]
```

The `not s` flip is the key detail: the backward chain was built travelling
right-to-left, so replaying it inside a left-to-right `calc` means reading every
step in the opposite direction — exactly toggling `.symm`. The two halves are then
concatenated, one `calc` line per edge, with the final line's target forced to `gr`
(the goal's right side as literally written) so the chain terminates on the goal
rather than on the normalized form.

Nothing is re-derived at collision time; the parent links already hold the proof.

### The output is always a single flat chain

No branching, no auxiliary lemmas, no combining two independently-derived facts.

**This is not an expressiveness loss in principle.** For pure equational reasoning,
if `L2 = R2` follows from `L1 = R1` at all then it follows by *some* sequence of
one-at-a-time rewrites — tree-shaped equational proofs always flatten into chains
(Birkhoff: derivability and rewrite-connectivity coincide).

**The cost of flatness is length**, and length hits the budget. A `have` lemma
proved once and used three times becomes a flat chain that redoes the work three
times, so a proof that is short with a lemma can sit far past `max_depth` without
one.

### The real limits (all in `gen`/`comps`, ~line 1955)

```python
def comps(sub):
    free = [v for v in e1v if v not in sub]
    if not free: return [dict(sub)]
    if len(free) > 3: return []              # gives up entirely
    pp = e2v if len(free) >= 3 else pool     # 3 free -> goal vars only
    for combo in _product5(pp, repeat=len(free)):
        ...
        if len(out) >= 200: break            # capped
```

Unifying the hypothesis against the current subterm pins down part of the
instantiation; the rest must be guessed. Hard limits:

- **more than 3 unpinned variables -> no rewrite generated at all**, position skipped
- with exactly 3, completions come only from the goal's variables, not the pool
- at most 200 completions per position
- generated terms dropped if `_tsize5(...) > 20` nodes
- plus `state_cap` (20k-500k, scaled by time budget), `max_depth`, wall clock

So the binding constraints are instantiation guessing and the term-size ceiling, not
the shape of the output. A valid chain passing through a 25-node intermediate is
invisible no matter how much time is allowed. And a failed search never means "no
proof exists" — only "not within these caps."

### The rest of eulerv5 is not flat

Only the BFS is. The hardcoded blob ships genuinely tree-shaped proofs with nested
lemmas and reused intermediates (see ~line 362):

```
have h1    : x = ((x ◇ x) ◇ x) ◇ (x ◇ x)                := h x x
have h2    : x ◇ x = (((x ◇ x) ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x) := h (x ◇ x) x
have hA_eq : (x ◇ x) ◇ x = (x ◇ (x ◇ x)) ◇ x := by ...
```

Those are precomputed from the mined corpus, not constructed by the BFS. Generating
that shape is left to the specialized engines and the LLM.
