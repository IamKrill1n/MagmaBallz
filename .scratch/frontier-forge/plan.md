# Frontier Forge: manufacture harder problems, mine the heuristics nobody has

Status: draft for approval
Owner: hungpk
Date: 2026-08-19

## Premise

Every existing corpus is nearly saturated. The current best solver takes 97.7%
of all 2,469 labeled pairs; our integrated solver just took the extra_hard lead
(193/200) and the union of known techniques covers extra_hard 200/200. The
labeled corpora can no longer tell us what we don't know.

Meanwhile the actual Stage-2 band is `eq_size5.txt`: 62,576 order-5 laws —
a ~3.9 billion ordered-pair space of which the corpora touch 2,469 pairs
(0.00006%). The held-back evaluation lives somewhere in that space. The way to
"go further beyond" is to hunt there ourselves, find the pairs our whole
portfolio fails, settle them with fresh mathematical work, and distill whatever
settled them into deterministic solver tiers.

The eq168/CG9 episode is the template — generalized:

    wall found by measurement → theory explains the wall → object found by
    targeted search → object named as a witness → +31 at zero marginal cost.

Frontier Forge industrializes that loop.

## The loop

```
FORGE      generate candidate pairs from eq_size5.txt
   │
SIEVE      run the full portfolio (m6sat, reja23, generalized as probes,
   │       cheap invariants, signature bank) at bounded budget
   │       → solved pairs: certificate = ground-truth label (free labels!)
   │       → UNSOLVED pairs: the Frontier Set — nobody's technique reaches them
   │
ASSAULT    per frontier pair, a Fable agent works the mathematics directly:
   │       model-theory analysis, structured search (A²=J-style
   │       characterizations), infinite constructions, proof synthesis —
   │       with Python + the local Lean judge as its lab
   │       → deliverable per settled pair: judge-accepted certificate
   │         + a technique note (what class of object/argument settled it)
   │
DISTILL    cluster technique notes → new named witnesses, new structured
   │       families, new lemma patterns, new invariants
   │
INTEGRATE  each distilled heuristic lands in EQT02-M00006.py as a gated tier,
           passes a paired sweep (≥1 gain / 0 losses), joins the regression set
           → loop back to SIEVE with a stronger portfolio
```

Key property: **no label oracle is needed.** A judge-accepted certificate IS
the label. The Frontier Set needs no labels at all — being unsolved is its
definition. This sidesteps the provenance problem the evaluation_* corpora
have (contributor-generated labels, unverifiable).

## Phase plan

### Phase 0 — Prerequisites (done or in flight)
- Judge built, harness green. ✅
- Scoreboard/paired-gate infrastructure. ✅
- Integrated solver as the portfolio core (+37 today). ✅
- Battery (order-≤4 byte-identity) completes. ⏳
- Commit of today's six steals. ⏳

### Phase 1 — FORGE + SIEVE v1 (deterministic, free)
1. Parse all 62,576 laws; compute cheap features (vars, op count, one-sided
   variables, leaf sequences, duality classes).
2. **Signature bank**: evaluate every law against the witness/model bank
   (all named witnesses incl. CG9, structured families n≤7, natural CGs,
   known ETP-style families). One bitset per law. A pair (E1,E2) is
   *model-separated* (FALSE, certificate ready) iff some bank model satisfies
   E1 and not E2 — this is the ETP's 524-witnesses trick run in reverse.
3. Candidate selection biased toward hardness: hypotheses with few variables
   + rich structure (eq168-like: sparse finite spectrum suspected), pairs NOT
   separated by the bank, NOT settled by invariants (variable multiplicity,
   leaf invariants, diagonalization), NOT proven by cp_saturation at elevated
   dosage.
4. Output: `frontier_v1.jsonl` — target 200–500 pairs the whole portfolio
   fails at (say) 60 s each. Budget: pure CPU, days of background time, $0.

### Phase 2 — ASSAULT (Fable agents, the new ingredient)
- One agent per frontier pair (batched; worktree-isolated scratch, shared
  read access to judge). Each agent must end in one of exactly three states:
  a) TRUE: judge-accepted proof certificate,
  b) FALSE: judge-accepted countermodel certificate,
  c) OPEN: a structured note on what was tried and why it failed.
- Agents get the full toolkit doctrine: symbolic analysis first (does the
  target hold in the free/natural model of E1?), characterization search
  (CG9-style: find the matrix/graph condition E1's finite models satisfy,
  enumerate small solutions), structured families, infinite Lean models
  (the judge goal has no finiteness hypothesis), saturation with real budget.
- Every certificate re-verified through judge.verify before it counts.
- Deliverables: `assault/<pair>/certificate.lean`, `assault/<pair>/technique.md`.
- Scale knob: start with 30 pairs as a pilot to calibrate cost/agent.

### Phase 3 — DISTILL
- Cluster technique notes: which settled pairs share the same *class* of
  object (a new witness table? a family parameterization? a proof pattern?).
- Rank by leverage: (pairs settled in frontier) × (estimated density in the
  full pair space, via the signature bank).
- Anything covering ≥3 frontier pairs becomes an implementation candidate.

### Phase 4 — INTEGRATE
- Each candidate lands as a gated tier in `EQT02-M00006.py`:
  witnesses → named table tier; families → structured-family generator;
  proof patterns → saturation seeding or a new route at correct priority.
- Gate: paired sweep on (frontier_v1 + all existing corpora), ≥1 gain /
  0 losses, docs updated, size ledger checked (500 KB cap; currently 138 KB).
- Settled frontier pairs join a permanent regression corpus
  (`frontier_regression.jsonl`) — labels are certificates, so it is
  provenance-clean in the way evaluation_* is not.

### Phase 5 — ITERATE
- Re-run SIEVE with the strengthened portfolio; the frontier moves outward.
- Stop condition per iteration: ASSAULT settle-rate drops below ~20% or
  DISTILL yields no candidate covering ≥3 pairs — then the remaining OPEN
  set is itself a product (candidate Austin pairs / genuinely hard cases,
  worth an upstream issue).

## Productions (deliverables checklist)

| # | Production | Form |
|---|---|---|
| P1 | Law feature table + signature bank | `.scratch/frontier-forge/bank/` + generator script |
| P2 | `frontier_v1.jsonl` | the harder test, 200–500 unsolved pairs |
| P3 | Assault harness | agent prompt template + verification loop script |
| P4 | Technique ledger | `techniques.md`, one entry per settled pair class |
| P5 | New solver tiers | gated code in `EQT02-M00006.py` + SOLVER_DOCS entries |
| P6 | Frontier regression corpus | certificate-labeled, permanent |
| P7 | Evidence pack v2 | updated published report |
| P8 | Upstream notes | issues for organizer corpora / remaining OPEN pairs |

## Guardrails

- **Certificates or it didn't happen** — no verdict without a judge-accepted
  artifact; agent claims are never trusted directly (the eulerv5 lesson).
- **Paired gates for every integration** — the +37 methodology, unchanged.
- **Determinism** — FORGE/SIEVE fully seeded and reproducible; agent output
  enters the solver only as static data/code, never as runtime dependence.
- **Provenance ledger** — every frontier pair records how it was generated,
  so we can argue it wasn't cherry-picked to flatter the solver.
- **Size budget** — distilled data competes for the remaining ~360 KB.
- **Cost control** — ASSAULT is the only expensive phase; pilot 30 pairs
  first, review settle-rate and per-pair cost before scaling.

## Open questions for the owner

1. ASSAULT scale/budget: pilot 30 agents, then how far?
2. Do we probe with reja23 in the SIEVE (their solver as a filter only,
   never as a source of code) — recommended yes.
3. Share OPEN pairs upstream (Zulip) or hold as competitive material?

---

## Amendment 1 — Hardness and novelty certification (owner discussion, 2026-08-19)

Hardness levels: H1 unsolved by integrated solver at full 3600 s budget;
H2 unsolved by every repo solver at full budget; H3 order-5-only (outside the
published ETP order-≤4 graph); H4 survives a doctrine-complete assault (the
full ETP technique catalogue executed and logged item-by-item). Frontier
membership requires H1–H3; H4 is certified during ASSAULT.

Novelty tiers: N0 new to our solver; N1 new to the repo; N2 new relative to
the ETP technique catalogue (checked against a Prior-Art Ledger: ETP
paper/blueprint chapters, upstream repo constructions incl. MagmaA2T.Facts,
literature); N3 new mathematics. Calibration: CG9 is N1, borderline N2
(objects in Knuth 1970; the named-witness weaponization is ours).
Core logic: a pair holding H4 can only be settled by something beyond the
catalogue-as-executed — the frontier manufactures the need for invention.
N3 candidate directions: a law→finite-model-characterization "spectrum
compiler"; a spanning model basis for the order-5 band; systematic invariant
generation; parameterized Lean-emittable infinite-model schemas.

## Amendment 2 — FORGE v2: adversarial generation with planted solutions

Replace/augment sampling with three seeded generator families:

- **G-TRUE (derivation walks)**: build DAG-shaped H-derivations u →* v of
  controlled depth/width/instantiation size; emit (H, u = v); the planted
  derivation is the certificate. Sieve still certifies hardness (shortcut
  proofs exist). Trace hygiene: canonical renaming, dualization, mixing.
- **G-FALSE (exotic-model planting)**: construct the witness first
  (generalized characterization solutions A^k = J, perturbation/exception
  models, skew products, orders 9/16 outside all banks); choose H ∈ Sat(M),
  G ∉ Sat(M); portfolio FALSE tiers must fail to find any smaller witness.
- **G-BREAK (assumption breaking)**: one generator mode per measured solver
  bet — gappy spectra (n ≤ 8 bet), mountain-pass proofs (term-size-cap bet,
  breaks every solver here), pool-alien instantiations, off-center meeting
  points (2+2 closure bet), textual-similarity inversions, rich 5-var laws.
  Provenance tags record which bet each pair attacks.

**Sealed-solution protocol**: planted certificates go to `sealed/`, invisible
to ASSAULT agents. Post-assault trichotomy: rediscovered (confirmed),
solved differently (two techniques for one pair), unsolved (a certified-hard
problem WITH a known answer — premium regression material, and an exact
statement of what heuristic is missing).

## Amendment 3 — The four levers: expand what the miners hunt for (owner, 2026-08-20)

The original ASSAULT mandate implicitly asked miners for ONE thing: better
heuristics, i.e. better *choices*. Measurement on 2026-08-20 says that is one
lever out of four, and historically not the strongest. The mandate is
**expanded, not replaced** — every miner still hunts ordering heuristics, and
now also reports findings under the other three headings.

**The four levers** (they differ in kind, not degree):

| Lever | Question | Risk profile |
|---|---|---|
| **REACH** | Is the solution even inside the space we search? | A GATE, not a multiplier. Outside reach → speed and ordering are both worth zero. |
| **REFORMULATION** | Can we swap the problem for an easier one whose solution transfers? | Cheap when it lands, no downside when it misses. |
| **ORDER** | Within reach, do we meet the right object first? | The classic heuristic axis. Safe ONLY as ranking. |
| **RATE** | How many nodes per second? | Pure engineering, uniform gain, no risk. |

**Measured evidence, 2026-08-20** (all judge-accepted):

- REACH: wide slack (8 → 20) + breaking the n ≤ 10 table ceiling → **14 cases**
  that no build of ours or reja23 had ever solved. Note the direction: we
  WIDENED. Narrowing the space would have lost all 14.
- REFORMULATION: heavy-ladder (prove a bridge, then close the goal — the
  bridge's small endpoints make the pruning caps bite in the right place) +
  systematic bridge enumeration → **7 cases and counting**.
- ORDER: semantic H-model filter just landed, unmeasured.
- RATE: untouched. And it is the largest single pool of waste we have measured
  — on a resisting problem, **96 % of wall-clock sits in the goal-closure step**
  (`proof_between_terms_guided`, re-run from scratch every round with the whole
  pool), against 4 % in candidate generation, scoring and selection.

**Hard rule falling out of this** (the slack-8 lesson, in one line): ORDER must
be applied as *ranking only*, never as cutting. Ranking changes what we meet
first; cutting changes what we can meet at all. A learned policy that prunes
re-creates exactly the trap that cost us 13 problems.

**Expanded miner deliverable.** Per settled pair, the technique note now
answers all four, and explicitly says "none" where there is nothing:

1. ORDER — what ranking signal would have found this sooner? (unchanged from v1)
2. REACH — what class of object or argument was structurally OUTSIDE our
   engine's representable space? This is the highest-value finding: name the
   gap, not just the fix. Example from today: `hard2_0027`/`hard2_0125` have
   many models of H at orders 8–12 in which the goal always holds — their
   witness is outside every small finite table, i.e. a reach gap, not a
   ranking failure or a speed failure.
3. REFORMULATION — was there an easier target (a bridge law, the dual problem,
   a meet-in-the-middle split) whose solution transfers to the goal?
4. RATE — what did the agent watch the engine waste time on?

Appraiser and red-team scoring is likewise extended: a technique that opens
REACH scores higher than one that improves ORDER by the same case count,
because reach gaps are gates — they block an entire class, permanently, and no
amount of later tuning recovers them.


## Amendment 4 — the Forge is insurance, not upside (owner, 2026-08-20)

The owner overruled a proposal to defer the Forge and the miner-derived
heuristics. The reasoning, quantified after the fact and confirmed:

**The headroom argument was conditional and the condition is unverifiable.**
Solve rates on the public corpora after 2026-08-20's work:

| Corpus | Rate |
|---|---|
| normal, hard1, evaluation_{normal,hard,extra_hard} | 100 % |
| hard3 | 99.5 % |
| hard2 | 98.5 % |
| evaluation_order5 | 97.5 % |

Projecting a 2469-problem private set drawn from a single difficulty band:

| Private set resembles… | Projected score | vs the 2460 estimate |
|---|---|---|
| `normal` | 2469 | +9 |
| `hard2` | 2432 | **−28** |
| `evaluation_order5` | 2407 | **−53** |

So the downside exposure to a harder-shifted private set (up to −53) is roughly
**six times** the entire remaining headroom on the observed distribution (+9).
Optimising against the observed distribution is optimising the small number.

**Consequence for the Forge's purpose.** Its deliverable is not "a few more
problems on the public sets". It is the only instrument we have that (a)
manufactures problems from the harder bands we are weakest on — order-5 and
hard2-style — so robustness there can be *measured* instead of assumed, and
(b) mines the techniques that band needs, under the anti-overfitting discipline
already specified (splits by hypothesis law, transfer ratio ≥ 0.5, sealed
vault, red-team pass).

**Consequence for miner targeting.** Priority order for frontier-set
composition is now: order-5 laws first (weakest band, 97.5 %), then hard2-style
absorption pairs (98.5 %), then everything else. Under Amendment 3 each miner
still reports across all four levers; Amendment 4 only changes which problems
they are pointed at.

If the private set turns out easy, this work costs time and nothing else. If it
is hard-shifted, it is the difference between 2460 and 2407.
