import JudgeProblem

-- [DUAL, luật nền eq2538] ETP model 1117: op a b = 2a - b/2 on Int (ediv). Base law eq1117.
-- Placeholder ((-10) : Int) ((-10) : Int) ((-10) : Int) is replaced per problem by the emitter.

def submission.op (a b : Int) : Int := 2 * a - b / 2

def submission.M : Magma Int := { op := fun a b => submission.op b a }

theorem submission.h1 : @EquationLHS Int submission.M := by
  intro x y z
  show x = submission.op z (submission.op (submission.op z (submission.op x y)) y)
  simp only [submission.op]
  omega

theorem submission.h2 : ¬ @EquationRHS Int submission.M := by
  intro h
  exact absurd (h ((-10) : Int) ((-10) : Int) ((-10) : Int)) (by decide)

def submission : Goal :=
  ⟨Int, submission.M, submission.h1, submission.h2⟩
