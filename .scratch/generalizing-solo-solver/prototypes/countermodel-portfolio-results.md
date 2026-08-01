# Countermodel portfolio prototype results

Status: PROTOTYPE — evidence for a planning decision, not production code.

## Question exercised

Which ordering of exhaustive small magmas, structured families, and
constraint-propagating backtracking provides the best FALSE-certificate coverage
per deterministic work allowance, and does retaining structured premise-models
improve backtracking? A hash-derived candidate lane was measured only as a
diagnostic because the settled deterministic-strategy contract excludes sampling.

## Method

- Corpus: all 145 FALSE-labeled cases in the `hard1` + `hard2` development
  benchmark. Labels selected the offline analysis slice and were not exposed to
  candidate generation.
- Exhaustive streams: all order-2 tables, then all order-3 tables.
- Structured stream: the suii0x-style constant, projection, min/max, affine,
  diagonal, rectangular-band, product-affine, and projection-exception families
  at orders 2 through 7, with exact table deduplication.
- Backtracking: deterministic row-major, value-ascending depth-first search at
  order 4, capped at 2,000 assigned-cell nodes per case. The seeded variant tries
  values from retained structured order-4 premise-models before the ordinary
  ascending order.
- Diagnostic sampling: 250 hash-derived tables at each order 4 through 7 after
  the other stages.
- Work counters: complete tables considered, equation assignments checked, and
  backtracking nodes. Equation-assignment checks are the better comparison than
  table count because checking an order-7 table is much more expensive than
  checking an order-2 table.

Run command:

```bash
python3 .scratch/generalizing-solo-solver/prototypes/countermodel_portfolio.py \
  --portfolio exhaustive_first_seeded \
  --max-backtrack-nodes 2000 \
  --pseudo-random-count 250
```

## Results

| Portfolio | Solved / 145 | Assignment checks | Tables considered | Backtrack nodes |
|---|---:|---:|---:|---:|
| exhaustive 2–3 → structured → cold backtracking | 97 | 20,798,116 | 2,355,130 | 106,558 |
| exhaustive 2 → structured → exhaustive 3 → cold backtracking | 97 | 33,892,901 | 1,691,332 | 106,558 |
| exhaustive 2 → structured → exhaustive 3 → seeded backtracking | 99 | 33,941,704 | 1,689,369 | 102,675 |
| exhaustive 2–3 → structured → seeded backtracking | **99** | **20,846,919** | 2,353,167 | **102,675** |

For the selected ordering, first discoveries were:

- exhaustive order 2: 6 cases;
- exhaustive order 3: 34 cases;
- structured families: 38 cases;
- seeded backtracking: 21 cases.

The witnesses had orders 2: 6, 3: 34, 4: 22, 5: 29, and 7: 8. The
hash-derived diagnostic tested 46,000 candidates across the 46-case final
residue and added no witness.

The cold/seeded control held stage order and node cap fixed. Seeded backtracking
added `hard1_0001` and `hard1_0024`, reduced total backtracking nodes from
106,558 to 102,675, and produced no losses. Exact cross-stage deduplication
skipped 31,836 duplicate table generations in the selected portfolio.

Two identical repeated 10-case runs produced byte-identical summaries, including
candidate counts, assignment checks, first-hit lanes, and unresolved IDs.

## Proposed reading

The prototype supports one opaque countermodel-portfolio strategy session with
this private stage order:

1. exhaust orders 2 and 3;
2. enumerate structured families at orders 4 through 7, cheap families before
   larger affine/product/exception families;
3. resume constraint-propagating backtracking at order 4, then higher orders only
   when later budget experiments justify them;
4. omit pseudo-random sampling from the admissible strategy.

The searches should share only bounded, deterministic search knowledge:

- an exact `(order, cells)` seen-table set;
- up to a small fixed number of structurally distinct premise-models per order,
  used as deterministic backtracking value-order seeds;
- normal resumable cursors and work counters owned by the strategy session.

They should not share scheduler-visible algorithm knobs or heterogeneous partial
frontiers. The kernel still owns candidate-level evidence deduplication and final
countermodel validation; internal table deduplication and premise-model reuse stay
behind the portfolio module's interface.

## Limits

- This is a public order-at-most-four proxy corpus and cannot establish held-back
  order-five generalization.
- The structured families and backtracker are representative throwaway ports,
  not optimized production implementations.
- A 2,000-node backtracking slice identifies ordering effects; it does not settle
  the later scheduler ticket's final credit allocation or order-5 cap.
- The diagnostic result does not prove all deterministic sampling schemes are
  useless. Sampling is excluded primarily by the already-settled reproducibility
  contract, with its zero additions here as supporting evidence only.
