# Analysis of the `AJ_stage1.md` strategy

## Summary

[`AJ_stage1.md`](./AJ_stage1.md) is best understood as a high-recall,
counterexample-first classifier rather than a complete decision procedure for
equational implication. It asks the LLM to:

1. search a deliberately varied portfolio of magma families;
2. validate a candidate counterexample;
3. return `FALSE` immediately when a witness is found; and
4. default to `TRUE` when the search is exhausted.

This is a strong shape for the Stage 1 task because Stage 1 requires only a
yes/no prediction, as described in the [competition README](../README.md#background).
A valid counterexample is decisive: one magma satisfying `E1` and falsifying
`E2` proves that `E1` does not imply `E2`. Failure to find a counterexample is
not decisive, but can still be an effective residual guess on a balanced
classification set.

The prompt generalizes from equations of order at most 4 to order-5 equations
because most of its useful tests are compositional functions of an equation's
syntax tree. They do not depend on equation IDs or a memorized implication
graph. Here, order refers to the number of binary-operation occurrences in the
equation; the repository distinguishes the order-at-most-4 law list from the
larger order-5 list in the [README](../README.md#background).

## Strategy breakdown

### 1. Projection and constant magmas extract cheap syntactic invariants

The first four models in [Step 1](./AJ_stage1.md) are simple but informative:

- In the constant magma, every non-leaf product collapses to the same value.
- In the left-zero magma, `x * y = x`, so a term evaluates to its leftmost
  leaf.
- In the right-zero magma, `x * y = y`, so a term evaluates to its rightmost
  leaf.
- In the wraparound magma, `x * y = x + 1 mod 3`, so evaluation follows the
  left branch while recording left-nesting depth modulo 3.

These are semantic implementations of syntax-tree fingerprints. The ETP-based
[research note](./equational-implication-strategies-and-theorems.md#cheap-theorems-and-invariants)
identifies leftmost leaf, rightmost leaf, ordered leaf sequence, and variable
multiplicity as useful implication obstructions. The projection magmas realize
the first two directly as small finite witnesses.

The key generalization property is recursion: adding another operation to a
term does not change the method. It only changes the path or leaf selected by
the evaluator.

### 2. Scalar affine magmas algebraically hash the term tree

[Step 2](./AJ_stage1.md) studies operations of the form

\[
x * y = ax + by \pmod n.
\]

Every term then evaluates to a linear combination of its variables. If
`C(t)` is the coefficient vector of a term, then

\[
C(s * t) = aC(s) + bC(t).
\]

Each variable occurrence contributes a monomial determined by the numbers of
left and right edges on its path through the term tree. Comparing the two
sides of an equation therefore checks several properties at once:

- variable multiplicity;
- placement of variable occurrences;
- left-versus-right nesting counts;
- depth information; and
- coincidences or distinctions modulo `n`.

The premise `E1` becomes a set of modular coefficient constraints. A choice of
`a`, `b`, and `n` that satisfies all constraints for `E1` but violates one for
`E2` gives a countermodel. This searches a whole parameterized family rather
than isolated Cayley tables.

Coefficient propagation is linear in the size of the term tree, apart from
small-vector arithmetic. That makes this stage naturally applicable to both
order-4 and order-5 equations.

### 3. Matrix coefficients recover noncommutative path order

Scalar coefficients commute, so two paths with the same counts of left and
right edges can collapse to the same monomial. [Step 3](./AJ_stage1.md)
replaces `a` and `b` with matrices `A` and `B`:

\[
x * y = Ax + By.
\]

Now a left-then-right path can contribute `AB`, while a right-then-left path
can contribute `BA`. Because these products need not agree, matrix-affine
models retain the order of turns through a nonassociative expression tree.

Conceptually, the two affine stages form a hierarchy:

- scalar affine models record path counts;
- matrix affine models can record path order.

That targets exactly the tree structure that distinguishes many magma laws.

### 4. The fixed model zoo is complementary

[Step 6](./AJ_stage1.md) adds models with deliberately different equational
behavior: a semilattice, Boolean NAND and implication, a central groupoid, a
BCK-style magma, rock-paper-scissors, a rectangular band, a nilpotent magma,
affine and Steiner operations, a truncated free magma, a Laver table, additive
models, and others.

Different families expose different features:

- semilattices test associative, commutative, idempotent collapse;
- rectangular bands retain outer coordinates;
- central groupoids select interior coordinates;
- rock-paper-scissors is commutative and idempotent but nonassociative;
- nilpotent operations collapse most nested computations;
- affine and additive models detect coefficient and multiplicity differences;
- Laver tables target left self-distributive behavior; and
- truncated free-magmatic constructions attempt to preserve raw term-tree
  distinctions up to a bound.

No one family is expected to separate every false pair. Their value comes from
covering different regions of the implication matrix. This resembles an
ensemble of classifiers, with an important distinction: when evaluation is
exhaustive and correct, each successful detector produces a mathematical
witness, not merely a probabilistic vote.

This reuse is supported by the ETP results summarized in the
[local research note](./equational-implication-strategies-and-theorems.md#decidability-and-semi-decidability-boundaries):
524 distinct finite witnesses refuted 96.3% of all false implications among
the order-at-most-4 laws. That does not guarantee the same coverage on unseen
order-5 cases, but it explains why a relatively small, diverse model bank can
be effective.

### 5. Partial-subterm construction and perturbation make search goal-directed

[Step 4](./AJ_stage1.md) tries to assign distinct values to intermediate
subterms of `E2`, keep its two sides separated, and complete unspecified table
cells with a sink. This informally approximates building a finite quotient of
the free magma modulo `E1`: preserve enough term structure to falsify the goal
while imposing the premise everywhere. The connection to the canonical free
model is described in the
[ETP-based research note](./equational-implication-strategies-and-theorems.md#free-magma-modulo-the-premise-one-canonical-model-decides-the-question).

[Step 5](./AJ_stage1.md) is a local adversarial search:

1. start from a simple magma already satisfying `E1`;
2. choose an assignment on which to attack `E2`;
3. mutate cells used by that evaluation, directing them to a safe-harbor
   element; and
4. retain only mutations under which `E1` still holds universally.

This is more targeted than sampling arbitrary operation tables. A random table
will often fail a nontrivial premise immediately, whereas perturbation searches
near a known premise-model and spends its effort on separating the goal.

### 6. Validation and prompt control reduce LLM failure modes

The prompt repeatedly instructs the model to evaluate from the inside out,
pause as soon as it finds a candidate, and run the Step 7 audit before accepting
that candidate. These instructions address common LLM errors in nonassociative
arithmetic: misreading parentheses, silently assuming associativity, or
reporting a table that does not actually satisfy the premise.

Other useful control mechanisms are:

- a fixed stage order, which discourages premature guessing;
- named models, which act as retrieval cues for known algebraic behavior;
- a scratchpad requirement for arithmetic;
- immediate candidate validation, which interrupts confirmation bias; and
- an exact output template, which makes the verdict easy to parse.

Step 0's request for ten resources may help by priming universal-algebra
concepts in the model's context. It supplies little case-specific evidence,
however, and consumes prompt and response tokens.

## Why the counterexample-first decision rule works

The semantic asymmetry is fundamental:

\[
M \models E1 \quad\text{and}\quad M \not\models E2
\quad\Longrightarrow\quad
E1 \not\models E2.
\]

An exhaustively checked counterexample therefore gives a sound `FALSE`
classification. Countermodel searches can have false negatives---they can miss
a witness---but should not have false positives when their evaluator and
universality check are correct.

The prompt maps all unresolved cases to `TRUE`. On a balanced set, if the
portfolio detects a fraction `r` of the false cases and all true cases reach
the default, the resulting accuracy is

\[
\frac{1+r}{2}.
\]

This rule converts countermodel recall directly into classification accuracy
without requiring the prompt to prove most positive cases.

## Reproduced small-model coverage

To measure how much of the behavior can be explained by the explicit model
bank alone, I mechanically evaluated the two 200-problem labeled reference
sets:

- [`evaluation_normal.jsonl`](../examples/problems/evaluation_normal.jsonl);
- [`evaluation_order5.jsonl`](../examples/problems/evaluation_order5.jsonl).

Both contain 100 true and 100 false cases. The reproduction used exact
inside-out term evaluation and exhaustive assignments for:

- the explicitly defined finite models M1 through M14;
- the order-4 Laver table `A2`; and
- every affine operation `a*x + b*y mod n` for `n` in `{3,4,5}` and nonzero
  residue coefficients `a,b`.

For each problem, the classifier returned `FALSE` if any tested magma
satisfied `E1` on every assignment but failed `E2` on at least one assignment;
otherwise it returned `TRUE`.

| Dataset | False cases detected | Accuracy with “counterexample else `TRUE`” |
|---|---:|---:|
| `evaluation_normal.jsonl` | 78/100 | 178/200 = 89.0% |
| `evaluation_order5.jsonl` | 83/100 | 183/200 = 91.5% |

This is not a reconstruction of the actual Stage 1 LLM score. It excludes the
matrix search, partial-subterm construction, perturbation search, proof attempt,
underspecified models, and infinite models. It shows that a relatively small,
fully mechanical subset of the prompt already explains substantial performance.
The slightly higher order-5 result also demonstrates that greater term size
does not necessarily defeat structural countermodel tests; additional tree
structure can create more opportunities for the models to distinguish `E1`
from `E2`.

## Why it generalizes well

The main reasons are:

1. **It operates on semantics and tree structure, not equation IDs.**
   Projections, affine coefficients, and structured models remain meaningful
   when another binary node is added.
2. **Its computations compose recursively.** Evaluating a longer term repeats
   the same local rule rather than requiring a new theorem template.
3. **Its model families are diverse.** Failures missed by an associative or
   commutative model may be exposed by a nonassociative, noncommutative, or
   collapsing one.
4. **Witnesses are reusable.** One model satisfying a premise and falsifying a
   conclusion can separate many equation pairs; the ETP's witness-bank result
   confirms that this reuse is substantial for the order-at-most-4 corpus.
5. **The decision rule matches the evidence asymmetry.** It demands positive
   evidence for `FALSE`, while using `TRUE` as a calibrated fallback rather
   than pretending bounded search proves implication.
6. **Longer equations offer more separating features.** Extra depths, paths,
   repeated variables, and nesting orders can make projection and affine
   fingerprints more discriminating, even though theorem proving may become
   harder.

## Limitations and sources of unsoundness

The cheatsheet is an effective heuristic, but its claim that every stage is
“formal and rigorous” is stronger than the prescribed procedure supports.

### Bounded audit is not always universal validation

Step 7 checks only

\[
N = \min(64, |S|^{|\mathrm{vars}|})
\]

assignments. When the total exceeds 64, passing the displayed audit does not
establish that `E1` holds for every assignment. The same issue appears in the
larger-carrier construction and perturbation stages. A purported
counterexample is sound only after all premise assignments have been checked
or a genuine algebraic proof of the premise has been supplied.

### Exhausting finite models does not prove implication

A false implication need not have a finite countermodel. The
[research note's discussion of Austin pairs](./equational-implication-strategies-and-theorems.md#finiteness-creates-extra-implications)
records implications valid in every finite magma but false in an infinite one.
Consequently, even exhaustive finite search at every attempted size cannot
justify a `TRUE` verdict for unrestricted magmas.

The default-positive rule is therefore a classification heuristic, not a
mathematical proof rule.

### The positive proof lane is underspecified

Step 8 says to “try to prove” the implication but provides no systematic
substitution, congruence, rewriting, saturation, or transitivity search.
Birkhoff completeness gives a complete semi-decision procedure for the true
side via enumeration of finite equational derivations, as summarized in
[the local research note](./equational-implication-strategies-and-theorems.md#birkhoff-completeness-semantic-consequence-equals-finite-derivability),
but the cheatsheet does not implement such an enumeration.

### Several model descriptions are incomplete or defective

- Step 3 does not specify the field or ring over which the matrices and vectors
  are interpreted.
- M15 names `S3` without specifying a binary operation.
- M16 does not provide the promised loop's Cayley table.
- M17 does not fully define how the truncation and null element interact under
  every product.
- M18 contains a corrupted character in the modular base case.
- M19 leaves the coefficient domain open; division by 2 is not available in
  characteristic 2.
- M13 and M14 are the same operation on `Z/3Z`, because
  `-y = 2y mod 3`, so they add no diversity relative to one another.

Finally, completing unspecified cells with a sink does not automatically make
`E1` hold. Every completed construction still requires a universal check or an
algebraic proof.

## Conclusion

`AJ_stage1.md` succeeds because it reframes a difficult theorem-proving task as
a sequence of cheap semantic fingerprints, parameterized algebraic tests,
targeted model-construction attempts, and a default-positive classification
rule. Its strongest components---projection invariants, affine interpretations,
noncommutative matrix interpretations, and a diverse reusable model bank---are
structural and compositional, which explains their transfer from order-4 to
order-5 equations.

The observed generalization should not be mistaken for a complete solver for
equational implication. It reflects a good match between this corpus, the high
availability and reuse of small countermodels, and the asymmetric evidentiary
value of a validated counterexample.
