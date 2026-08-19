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
