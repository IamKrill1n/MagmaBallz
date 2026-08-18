# Equation-list order versus implication topology

## Conclusion

**Do not treat equation IDs, or the line order of `data/equations.txt`, as a
topological order of the implication graph.**  The primary sources inspected
establish a numbered enumeration of equations and a separately maintained
implication graph, but do **not** state that the enumeration was generated
from that graph or satisfies a topological-order invariant.  The blueprint
index itself only exposes a link labelled “Dependency graph”; it contains no
claim about the numbering or the text-list order.

## What is established

- The project's official README describes its subject as equational theories
  “ordered by implication” and says that it initially enumerates 4,694 laws
  (up to symmetry and relabelling).  It links separately to the Lean and plain
  text equation lists, and separately to graph visualizations.  Thus equation
  IDs identify members of an enumeration; the implication relation is separate
  project data.  [Official README](https://github.com/teorth/equational_theories#equational-theories-project)
- The official raw `data/equations.txt` begins with the textual sequence
  `x = x`, `x = y`, `x = x ◇ x`, …, confirming that the file is an ordered
  enumeration.  This observation does not establish why that order was chosen
  or any relationship to implication edges.  [Official equation list](https://raw.githubusercontent.com/teorth/equational_theories/main/data/equations.txt)
- The published blueprint's table of contents includes a distinct “Dependency
  graph” link, but no statement that list order or IDs are a graph topology.
  [Blueprint index](https://teorth.github.io/equational_theories/blueprint/index.html)

## Consequences for an oracle

- There is no sourced guarantee for either edge orientation convention from
  equation number (whether a lower number implies a higher number, or the
  reverse).  An implication edge must be read from the graph/edge data itself.
- A topological ordering is only defined for a DAG.  Implication between
  individual equations can contain mutually implying/equivalent equations, so
  it would require quotienting or condensing strongly connected components
  before a global DAG order could even be asserted.  No inspected source says
  the list performs that step.
- Even if a current snapshot happened empirically to respect some edge
  direction, the sources found provide no stability contract for that property
  across regeneration or corpus revisions.  It must therefore be treated as
  an unverified optimization hypothesis, never as oracle correctness logic.

## Exact answer to the proposed claim

The claim is **not established by the blueprint website**.  Based on the
primary sources checked, the safe contract is: corpus IDs/line positions are
enumeration metadata; determine implication direction and topology only from
the implication graph data, and verify any acceleration against content
fingerprints.
