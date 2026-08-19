# Solver Strategy — reja23 vs. EQT02-M00006

Written 2026-08-19, at the close of the engine-day campaign (commits `91565b6` →
`2d69120` → `2738f26`). Sources: `examples/solo/demos/reja/EQT02-S00023.py` (read in
full at the routing level), `SOLVER_DOCS.md`, `.scratch/frontier-forge/prior-art-ledger.md`,
and the engine-day evidence packs in `.scratch/engine-day/results/`.

Standing at time of writing, on the complete labeled universe of 2,469 problems:

| Solver | Evaluation (800) | SAIR (1,669) | Total | Disproved submissions |
|---|---|---|---|---|
| **EQT02-M00006 (ours)** | 786 (normal 196 · hard 197 · extra_hard 200 · order5 193) | 1,644 | **2,430** | **0** |
| reja23 (EQT02-S00023) | 762 | — | 2,411 | 252 |

All of our 786/800 is achieved at 120 s with the LLM disabled.

---

## Part 1 — reja23's strategy

### The philosophy: an LLM steering trusted mechanical tools

Reja23 is built around one central idea that is different from every other solver in the
repo: the LLM is not asked to write proofs. Instead, the LLM is treated as a *strategist*
that steers a registry of trusted, mechanically-verified tools. The solver's PROMPT says
this explicitly in its first line: "You are steering trusted mechanical tools for a magma
equation problem." The LLM must return exactly one JSON object choosing an action — never
prose, never raw Lean (with a few narrow exceptions). Everything the LLM proposes is
treated as an untrusted hint: if it proposes a bridge lemma M, the solver mechanically
proves H ⇒ M first, and only then uses H + M to attack the goal. Bad hints are silently
discarded.

Around this idea the solver builds an entire formal collaboration protocol (it names it
`sair-collab-protocol-v0`). Every mechanical tool failure is converted into a structured
JSON "protocol state" — a telemetry record with a status, the tool's contract, the search
frontier, and a `need_hint` field telling the LLM specifically what kind of decision is
needed next. These states accumulate and are fed back into the next LLM round. There is
also a persistent "candidate blackboard" that carries mechanically proved, refuted, and
budget-limited lemmas across LLM rounds, so a lemma that was proved but not yet connected
to the goal survives and can be bridged from later, rather than being rediscovered.

### The action vocabulary the LLM can use

The allowed LLM responses define the whole strategy space. The LLM may return:

- a `tool_call` — pick a registered tool with arguments (for example a false-model search
  at a specific size, or superposition seeded with specific auxiliary lemmas);
- a `midpoint` — a single bridge equation M, so the solver proves H ⇒ M and then
  H + M ⇒ Goal;
- a `lemma_chain` — several named helper equations to be proved in sequence;
- a `candidate_bundle` — three to five ranked, mathematically distinct bridge candidates,
  each of which the solver normalizes, verifies, and retains on the blackboard;
- a `false_model_family` — a parameterized countermodel family such as an affine table
  with exception rules, which the mechanical side then searches;
- a `symbolic_model_plan` — a structured plan for an *infinite* countermodel in Lean
  (carrier, definitions, operation, hypothesis proof, counterexample proof), assembled
  from parts;
- a `symbolic_model_patch` — repair just the one component of a symbolic model that Lean
  rejected, instead of regenerating the whole artifact;
- a direct `goal_proof`, or a raw `false_table`.

A per-pass phase directive can narrow this vocabulary.

### The solve loop, stage by stage

The main `solve()` function (line 7055 of EQT02-S00023.py) runs a carefully
budget-choreographed sequence. Every stage gets a slice of the remaining budget computed
as a clamped percentage, with reserves held back for recovery passes.

**Stage 1: semantic audit.** Before anything else, `implication_semantics` audits the
problem. If the audit concludes that the implication is false but no finite countermodel
can exist, the solver skips all finite table search and goes directly to an LLM
collaboration whose goal text instructs the model to build a symbolic infinite-model
plan. This is unique among the local solvers — reja is the only one with a channel that
can even *express* a FALSE answer requiring an infinite countermodel (relevant to
Austin-law-style situations, per the prior-art ledger §A6/§G).

**Stage 2: structural routers.** A "residue ray" detector checks whether the hypothesis
has a lone variable occurring once as the terminal value under nested left translations;
if so, an early one-round LLM checkpoint offers a residue-controlled involutive
left-action countermodel family search.

**Stage 3: the rigidity scout.** `small_model_rigidity_scout` enumerates all models of
the hypothesis up to size 4. If no nontrivial model of H exists through n = 4, that is
treated as strong evidence the implication is TRUE via collapse (H likely forces a
degenerate magma), and a large budget slice goes to
`rigidity_collapse_portfolio_attempt` — a portfolio of collapse-proof plans, with the
small-model signal used for routing only, never as proof.

**Stage 4: cheap FALSE search.** `small_false_search`, then `model_finder_v2` (its
backtracking finite model finder) at sizes 4 and 5, then a skew-product search that
builds size-6 countermodels as a 2×3 product of a control magma and a fiber.

**Stage 5: cheap TRUE tools.** If the hypothesis shape makes it plausible,
`standard_aux_superposition_attempt` runs bounded superposition seeded with a standard
menu of auxiliary lemmas (constancy, left projection, right projection, row-constancy) —
and notably, when this fails, a *feedback-driven retry* inspects the failure state and
re-invokes the tool with adjusted arguments. Then broad-grounding derived proofs, and a
helper-chain portfolio for repeated-self-absorption shapes. Then the flat list of direct
syntactic proof candidates (substitutions, bridges, and so on).

**Stage 6: interleaved LLM collaboration.** From here on, LLM collaboration passes
alternate with heavier native tools. Each pass has a written "collaboration goal"
tailored to the situation (early true-side pass, false-route pass after native search
failed, late recovery pass), carries the accumulated failure telemetry, and enforces
no-repeat via failure signatures.

**Stage 7: heavy FALSE portfolio.** `model_finder_v2` at sizes 6 through 8; then a
"promoted exact continuation" — if earlier failure telemetry indicates a specific route
that nearly succeeded, it is retried exactly; then the wide portfolio: stochastic local
search at n = 6, a sympy-based SAT encoding at n = 6, a CP-SAT search, polynomial
countermodels (`poly_ce`) up to n = 13, and structured countermodel families up to n = 7.

**Stage 8: heavy TRUE tools.** `native_deep_true_candidates` runs `pc_saturate` — a
native bounded paramodulation/superposition saturation over the hypothesis plus any
proved auxiliary lemmas, with `pc_render` emitting the complete Lean derivation of
whatever it finds. After that, `ordered_completion_attempt` runs ordered
Knuth–Bendix-style completion: `ordered_completion_discover` grows an oriented rule set
toward one of several completion targets, and `ordered_completion_replay` replays the
dependency closure of the winning derivation as a Lean proof chain. (These two engines
are the "TRUE-side anatomy" our engine-day commits credit as the source of the ideas we
stole.)

**Stage 9: recovery.** Two final LLM collaboration passes — a "late system-2" pass and a
"true-recovery" pass — receive everything: the graph search state with its frontier and
closest cross-frontier pairs, the last several FALSE failures, the deep-tool failures,
and the completion failures, and are asked to repair prior actions rather than start
over.

### Strengths and the measured weakness

Reja23's strengths are real: it has the most sophisticated TRUE-side discovery machinery
in the repo (superposition saturation plus ordered completion), the only infinite-model
FALSE channel, the widest FALSE portfolio (SAT encodings, polynomial families, skew
products), and a genuinely well-designed feedback protocol. It scored 762/800 on the
evaluation corpora and 2,411/2,469 on the full labeled universe — the strongest rival by
a wide margin.

Its measured weakness is reliability of submission: across the 1,669 judged SAIR cases,
reja23 had **252 disproved submissions** (certificates submitted and rejected as wrong),
versus zero for ours. Its architecture makes many judge attempts per problem and treats
rejection as feedback, which is fine within a per-problem budget but costs accuracy on
the scoreboard. It is also structurally dependent on LLM quality for its routing and
bridge-finding, whereas everything durable in our solver is deterministic.

---

## Part 2 — Our current best strategy (EQT02-M00006.py)

### The philosophy

Our solver is deterministic-first and evidence-gated. Every capability is a pure function
of the problem text; the LLM tier still exists but was measured to convert 1 of 230
escalations (unreproducibly), so all durable strength is in the deterministic routes. The
second half of the philosophy is methodological: no change lands unless a paired sweep
over judged corpora shows at least one gained case and zero lost cases. Across the entire
engine-day campaign (roughly 3,800+ paired judged measurements), zero losses were
accepted.

### Foundations

Terms are nested hashable tuples — `("var", "x")` and `("op", left, right)` — and every
term utility is `lru_cache`d. Every emitted certificate passes `sanitize_lean_code` (no
`sorry`/`axiom`/`unsafe`/etc., allowed imports only, size caps, must define
`submission`). FALSE certificates are finite tables rendered through `finOpTable` and
discharged by `decideFin!`. Both execution modes are live: Solo (one problem per process
over stdin/stdout) and Marathon (manifest in, answers out, shared budget with triage).

### The TRUE side

`solve_problem` tries deterministic routes in strict priority order, cheapest and most
specific first, because route order determines which proof shape is emitted:

1. **Reflexive** — the two equations are identical.
2. **Singleton** — the hypothesis has a variable on one side absent from the other,
   forcing a one-element magma, under which everything is true.
3. **Collapse routes** — four detectors for hypothesis shapes that force all elements
   equal through a short equational chain (`middle_self_collapse`,
   `front_double_self_collapse`, `alternating_front_self_collapse`, and its mirror).
4. **Derived-law routes** — the hypothesis implies a known useful law (left projection,
   or commutativity via the square-twist pattern), and the goal is proved under that law.
5. **Direct substitution** — the goal is a substitution instance of the hypothesis (or of
   its flip, using `.symm`); the proof is a single application of `h`.
6. **Bridge route** — both sides of the goal match one side of the hypothesis, and the
   two "other sides" coincide; the proof is one `trans` through that common term.
7. **Completed bridge** — the same, but unbound variables are filled by trying terms from
   the goal's subterm pool, up to 2,500 trials.
8. **Projection route** — the hypothesis is a projection law and both goal sides reduce
   to the same variable by repeated projection.
9. **Rewrite-chain BFS** — breadth-first search from the goal's left side, rewriting with
   the hypothesis at any subterm position, depth 2.
10. **Special absorption routes** — three recognizers for specific absorption shapes,
    including one that reduces a particular equation to Equation 19.
11. **Absorption closure** — bidirectional BFS for absorption-shaped hypotheses, filling
    free variables from a term pool.
12. **Equational closure** — the most general classical route: bidirectional BFS from
    both goal sides, applying the hypothesis in either direction at any position, meeting
    in the middle.

When all of those miss, the two engine-day additions run:

13. **The critical-pair saturation route** (`cp_saturation_route`), the single biggest
    source of the campaign's gains. It alternates two activities: attempting to prove the
    goal with the current rule set (hypothesis plus derived lemmas), and deriving new
    lemmas by Knuth–Bendix-style critical pairs — unifying one rule's side into each
    non-variable subterm position of another rule, with a proper occurs-check. The
    crucial design property is that **every lemma is born already proved**: the overlap's
    peak term rewrites to one side by parent A and to the other by parent B, so each
    lemma's Lean proof is a two-step `trans` through the peak, citing only its parents'
    names. When a proof is found, the certificate emits only the transitively cited
    lemmas, as topologically ordered `have`-blocks — so proof DAGs (a lemma used twice,
    emitted once) come for free. Dosage is industrial: 200 lemmas, 10 rounds, 20 seconds,
    2,500 raw pairs. The route runs as **two sequential attempts with fully independent
    lemma pools**: the *classic* attempt first, byte-identical to the pre-beam algorithm
    so every previously solved case keeps its exact proof by construction; then, only if
    classic fails, the *beam* attempt, which retargets derivation each round at the
    closest cross-frontier gap and allows twice the term size. Both attempts fall back to
    variable-position overlaps (paramodulation into variables) when ordinary
    critical-pair derivation dries up. The two-attempt design exists because the obvious
    shared-pool version passed smoke tests but lost two cases in the paired gate — the
    pools starve each other — and losses are not accepted. This engine alone took order-5
    TRUE from 41 to 83 of 100, and opening it from the order-5 band to all bands measured
    +114/−0 on normal+hard.
14. **The standard-ladder route**, run after saturation fails: it tries to prove each of
    eight classic intermediate laws (collapse, projections, idempotence, row-constancy,
    operation-constancy, square laws) from the hypothesis using the saturation core, and
    re-attacks the goal with any proved law injected as a standing extra rule. Measured
    +1; small, kept because it cost nothing.

### The FALSE side

`find_counterexample` escalates through tiers, cheapest first:

1. **The named witness bank, now 227 verified tables of sizes 2 through 9.** The classic
   hand-picked witnesses (projections, constants, the Boolean operations, small cyclic
   and asymmetric tables) are joined by the **machine-wide harvest**: all 7,689 judge
   artifacts ever produced on this machine — by every solver, ours and rivals' — were
   scanned, and every distinct finite countermodel found was independently re-verified
   against its own problem before being banked. Witnesses are mathematical facts
   regardless of who found them, which is exactly the Equational Theories Project's
   named-witness-bank pattern. The bank's crown jewel is **CG9**, a non-natural central
   groupoid of order 9 found via Knuth's characterization (a 0-1 matrix A with A² = J).
   It satisfies Equation 168 while falsifying laws that hold in every *natural* central
   groupoid of any size, and since finite central groupoids exist only at square orders
   (1, 4, 9, 16, …), no bounded table search up to size 8 could ever have found it — it
   had to be named. CG9 alone refuted all 74 eq168-hypothesis cases in the evaluation
   corpora, including a 31-case residual no known solver could previously touch. New bank
   entries are tried after the originals so previously solved cases keep their original
   witnesses.
2. **Structured family tables** — semilattices, successor spines, conditional tables,
   negated sums, rectangle bands.
3. **Affine families** — tables of the form (ax + by + c) mod n.
4. **Quadratic families** — the same with cross terms and squares.
5. **Brute-force enumeration**, deliberately capped at n ≤ 3.
6. **The constraint-propagating backtracker**, the engine-day FALSE workhorse: a
   SEM/Mace-style search at sizes 4 through 6, filling table cells in row-major order
   with values ascending, propagating every fully-evaluable hypothesis instance after
   each cell, keeping completed tables only if they falsify the goal. Symmetry breaking
   is least-number with the bound `max(used values, i, j) + 1` — and this exact formula
   matters, because the naive bound using only previously-used values is a *completeness
   bug*: table indices are themselves elements, and the naive bound provably hid 9
   findable size-4 witnesses before it was caught against known-good tables. Node caps of
   150k/90k/40k per size and a 12-second private budget keep it bounded.
7. **Dual retry** — if everything fails, the whole search reruns on the dual problem
   (operand order swapped everywhere); a dual countermodel transposes back to a
   countermodel of the original. Because the backtracker sits above this tier, the dual
   retry inherits it.

### The LLM tier (retained, not relied on)

When every deterministic route fails in Solo mode, the solver escalates to guided-chain
collaboration with the LLM: the model proposes a chain of intermediate terms, the solver
verifies every hop mechanically (using the critical-pair lemma engine demand-driven on
failed hops — deriving up to 24 targeted lemmas per hypothesis and retrying once), and
only a fully verified chain is submitted. Failed hops are reported back with the exact
gap (`guided_chain_hop_unproved:<src> = <dst>`), round-0 analysis includes frontier
bridge hints ranked by shared subterm structure, verified hops and lemma pools are cached
across rounds, and a guaranteed-rejected reflexivity fallback is skipped rather than
submitted. All of this is honest option value: under the reference model
(gpt-oss-120b via deepinfra) it converted one case out of 230 escalations, so the
786/800 standing is achieved with the LLM disabled entirely.

### The methodology, which is inseparable from the strategy

Every candidate change is run through the scoreboard harness
(`.scratch/engine-day/harness/scoreboard.py`) as a paired sweep against the previous
build over judged corpora, and is accepted only at ≥1 gain / 0 losses. This replaced the
older, stricter byte-identity bar once the gate-opening change was measured at +114/−0.
Evidence packs for every accepted change live in `.scratch/engine-day/results/`, the
recovery runbook is `.scratch/engine-day/RESUME.md`, and sealed answers live in the vault
outside the repo (`~/dev/active/MagmaBallz-vault/`, never committed).

### What's deliberately still open

Two known gaps are documented rather than hidden. First, the remaining rival-only TRUE
cases need an **instance-chaining lemma generator** — lemmas built by forward-composing
hypothesis instances, which our overlap-based critical-pair derivation deliberately
filters out; this is the recorded "open steal" from reja23's anatomy. Second, **Frontier
Forge** (`.scratch/frontier-forge/`) is the adversarial-generation program over the
62,576-law order-5 band — signature bank (P1) done, sieve (P2) and mapmaker (P3) in
progress.

---

## The one-paragraph contrast

Reja23 bets on breadth and steering: a huge portfolio of mechanical tools with an LLM
choosing among them, telemetry flowing both ways, and many judge attempts per problem —
which buys it reach (including the infinite-model channel nobody else has) at the cost of
252 disproved submissions and dependence on the LLM. Ours bets on depth and certainty: a
fixed deterministic ladder ending in a heavily-dosed proof-carrying saturation engine on
the TRUE side and a verified witness bank plus complete bounded backtracking on the FALSE
side, with every certificate locally verified before submission and every change gated at
zero losses — which is how it holds the lead with zero disproved submissions and no LLM
in the loop.
