You are a mathematician specializing in equational theories of magmas.
Your task is to determine whether E1 {{ equation1 }} implies E2 {{ equation2 }} over all magmas.
 
This is a difficult problem that may require advanced techniques from universal algebra resources. Hence, you MUST follow steps 0-8 below in order, and your reasoning for each must be complete, formal and rigorous. You will lose points if you do not do everything in the steps. Always evaluate expressions from the inside out. If you find a POTENTIAL counterexample in Steps 1-6, immediately pause that step and execute Step 7 inline to validate it. If it becomes a VALIDATED COUNTEREXAMPLE, skip all remaining steps and go directly to the Output. If it fails validation, write 'Candidate invalidated' and resume exactly where you left off in Steps 1-6.
CRITICAL: Because you must evaluate math inside-out without making mistakes, you must use a <scratchpad> block to write out your step-by-step arithmetic before finalizing your conclusion. Only after doing the math in the scratchpad should you state your conclusion.
 
Step 0: List ten resources that can help us understand how to solve this, and similar, questions.
 
Step 1: Check for counterexamples (algebraically, or exhaustively over assignments for at most 3 variables and $\|S\| \leq 3$) using the magmas: 
M1. Constant-Magma: $x*y=0$, $S=\{0,1,2\}$
M2. 3x3 Left-Zero: $x*y=x$, $S=\{0,1,2\}$
M3. 3x3 Right-Zero: $x*y=y$, $S=\{0,1,2\}$
M4. Wraparound: $x * y = (x + 1) \pmod 3$
 
Step 2: Check if magmas defined on the additive group $\mathbb{Z}_n$ by an abstract affine binary operation $$ax+by  \pmod n$$, where $a,b,n \in \mathbb{N}$ and $n > 2$ can be counterexamples by doing: 
a. Determine conditions for E1 to hold universally (use only E1). 
b. Determine conditions for E2 to hold universally (use only E2). 
c. See whether there is a set of $a,b,n$ such that: $a, b > 0$, $n > 2$ that satisfy all the conditions found for E1 and that DON'T satisfy at least one of the conditions found for E2. If there is, test this set as a counterexample. If there isn't continue to the next step.
You must show your full work, formally (including stating all $a,b,n$ choices).
 
Step 3: Check Bilinear Matrix Magmas defined by $$x*y = Ax + By$$ where $A, B$ are 2x2 matrices, not necessarily commutative, as counterexamples by doing: 
a. Determine conditions for E1 to hold universally (use only E1). 
b. Determine conditions for E2 to hold universally (use only E2). 
c. Check if there are matrices $A, B$ that satisfy all the conditions found for E1 and that DON'T satisfy at least one of the conditions found for E2. If there are, test them as counterexamples. If there aren't continue to the next step.
You must show your full work, formally (including stating all $A, B$ choices).
Recall to perform replacements carefully, step-by-step, and (CRUCIALLY) from the inside-out.
 
Step 4: Construct a magma based on the Modified Partial Subterm Algebra for E2. You MUST:
a. Define an assignment for E2 variables that will be used to refute that it holds.
b. Define the magma, including the set $S$ and its operation $*$. When defining the Cayley table, if an operation $a * b$ is not explicitly required to satisfy E1 or fail E2, set $a * b = c$, where $c$ is a 'sink' element that helps satisfy E1. This prevents the magma from accidentally satisfying E2.
c. Check if this is a counterexample (i.e., E1 must hold for all assignments (algebraically, or exhaustively over assignments for at most 3 variables and $\|S\| \leq 3$)) with values from $S$ (as usual) and E2 is expected to fail for the specific assignment defined in a). 
Useful trapdoors are: $u*v=0$, $u*v=u$, $u*v=v$, $u*v=constant$. Test all of these trapdoors.
 
Step 5: For each of the finite magmas in Step 1 for which E1 held (the "Base"), use the Perturbation Method (Exception Method) as follows:
a. Define a new $S$ that has a number of elements greater than the number of distinct variables in E1 and E2 (e.g. if there are 3 distinct variables, then $S$ should have at least 4 elements). The operation $*$ remains of the same form as the original magma, but now it is defined over the new $S$. For example, if the original magma was a 3x3 left-zero, then the new magma will be a 4x4 left-zero.
b. Choose an assignment for all variables and show what E2 looks like with those assignments, i.e. its evaluation tree (e.g. in $(1 * 1 = 1 * (2 * 1)) * 1$).
c. Define a "Safe Harbor" element in $S$ -- this will be the element all exceptions will be mutated to (i.e. any override of the current * will be using this element).
d. While both E1 and E2 hold, mutate the value of the next innermost operation in E2 that has yet been mutated (e.g. $2 * 1$ in the above example) from its original value to the "Safe Harbor" element, but ensure that the behavior of the "Safe Harbor" doesn't change from its Trivial Base operation (e.g., for Left-Zero, if $3$ is a "Safe Harbor", then $3 * a = 3$) so it doesn't create new, unmapped exceptions. Tip: Avoid mutating "Diagonal" cells ($x*x$), if possible, to preserves stability in E1.
e. After each mutation, check if E2 fails for the assignment and if E1 holds for ALL assignments (algebraically, or exhaustively over assignments for at most 3 variables and $\|S\| \leq 3$) -- if so, it's a counterexample. If both E1 and E2 hold, then return to d and add another mutation (ideally of the next most nested operation in E2's evaluation tree). If E1 fails, revert the mutation and try either mutating the next innermost operation instead or mutating the most recent one to a different value. 
 
Step 6: Check for counterexamples (not exhaustively over assignments if there are more than 2 variables and $\|S\| > 3$) using the magmas: 
M5. Max-Semilattice (Chain Magma): $x*y = \max(x,y)$, $S=\{0,1,2\}$
M6. NAND Boolean Magma (Sheffer Stroke): $x*y = 1 - (xy)$, $S=\{0,1\}$ (standard multiplication/subtraction)
M7. Knuth's Central Groupoid (The "Inside-Out" Magma) -- the smallest non-trivial version is Order 4, over $S = \{0,1\} \\times \{0,1\}$, and the operation is defined by "taking the inner halves": $(a,b) * (c,d) = (b,c)$. The Trap: It perfectly satisfies the identity: $$(x * y) * (y * z) = y$$
M8. The BCK Logic Magma (The Hierarchy Builder): $S=\{0,1,2\}$. It acts like non-symmetric set difference or logical implication: $x * x = 0$, $0 * x = 0$, $x * 0 = x$, $2 * 1 = 1$, but $1 * 2 = 0$. The Trap: It perfectly satisfies the complex logical deduction identity:$$((x * y) * (x * z)) * (z * y) = 0$$
M9. Implication Magma: $x*y = \min(1, 1 - x + y)$ , $S=\{0,1\}$
M10. Rock-Paper-Scissors Magma: $S=\{0,1,2\}$. $x*x = x$. For distinct elements, $x*y$ evaluates to the "winner" of the two, where $1$ beats $0$, $2$ beats $1$, and $0$ beats $2$.
M11. Order 4 Rectangular Band: $S = \{0,1\} 	imes \{0,1\}$. The operation is $(a,b) * (c,d) = (a,d)$
M12. Nilpotent: $x*y = 0$ except $2*0=1$, $S=\{0,1,2\}$
M13. Idempotent Affine: $x*y = 2x-y \pmod 3$, $S=\{0,1,2\}$
M14. Order 3 Steiner Quasigroup ("Squag"): $x*y = 2x + 2y \pmod 3$, $S=\{0,1,2\}$
M15. "Symmetric Group" magma $S_3$
M16. Smallest Non-Associative Loop (Order 5): $S=\{0,1,2,3,4\}$. $0$ is the identity element ($x*0 = 0*x = x$). The rest of the Cayley table forms a Latin square such that the structure is non-associative.
M17: Truncated Free Magma ($F_k$): The Free Magma where all terms of depth $> 3$ are identified with a single null element $\perp$
M18. The Laver Table (The Self-Distributive Trap): A magma of order $2^n$ -- use the smallest non-trivial one ($A_2$) which has $S=\{1,2,3,4\}$ and is defined by the base case $x * 1 = (x mod 4) + 1$, and then recursively built using the identity $x * (y * z) = (x * y) * (x * z)$
M19. Medial Magma ($x*y = \\frac{x+y}{2}$ over $\mathbb{Q}$ or a finite field)
M20. Natural Numbers: $(\mathbb{N}, +)$
 
Step 7: If (and only if) a counterexample was found in Steps 1-6, you must perform the following Mandatory Mechanical Audit
a. Count the number of possible assignments ($\|S\|^{\\text{\|vars\|}}$). Set the minimum between 64 and the number of possible assignments to be $N$. Construct a markdown table for E1 showing one row per assignment for $N$ assignments with the following columns: "LHS", "RHS", "LHS=RHS?". You are strictly forbidden from using phrases like "by symmetry" or "similarly" when calculating the value of each assignment, which must be done carefully and step-by-step. If one row show that "LHS=RHS?" has a 'No' entry then state clearly that the counterexample failed, and resume your search linearly by moving to the next un-tested magma or the next step or the next item (a/b/...) within a step. Otherwise, proceed to b below.
b. Run a step-by-step E2 trace: For the specific assignment that fails E2, write out the calculation evaluating exactly one binary operation per line. If the LHS of E2 equals the RHS, then state clearly that the counterexample failed, and resume your search linearly by moving to the next step or the next item (a/b/...) within a step. Otherwise, proceed to c below.
c. Declare the potential counterexample a "VALIDATED COUNTEREXAMPLE."
 
Step 8: If (and only if) A VALIDATED COUNTEREXAMPLE was not found earlier, then provide a verdict of TRUE and try to prove that the claim is indeed TRUE, remembering to work carefully and from the inside-out.
 
Output Template (Follow this EXACTLY):
 
REASONING:
Step 0: [Your list of resources]
Step 1: [Your analysis]
... (continue through Step 8 or until a VALIDATED COUNTEREXAMPLE is found)
 
VERDICT: [TRUE or FALSE]
 
PROOF:
[Insert formal proof here if TRUE, otherwise leave empty]
 
COUNTEREXAMPLE:
[Insert magma definition and failure case here if FALSE, otherwise leave empty]
 
COUNTEREXAMPLE ID:
[Insert magma ID or Step ID where counterexample was found, e.g. M1, M2, Step 2, etc. if FALSE, otherwise leave empty]