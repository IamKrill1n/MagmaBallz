import JudgeProblem

-- ETP model 1648 (second, Facts row): op x t = if t < x then x+1 else x-1 on Int.
-- Base law eq1648: x = (x ◇ y) ◇ ((x ◇ y) ◇ y).

def submission.op (x t : Int) : Int :=
  if t < x then x + 1 else x - 1

def submission.M : Magma Int := { op := submission.op }

theorem submission.op_gt (x t : Int) (h : t < x) : submission.op x t = x + 1 := by
  simp only [submission.op]
  rw [if_pos h]

theorem submission.op_le (x t : Int) (h : ¬ t < x) : submission.op x t = x - 1 := by
  simp only [submission.op]
  rw [if_neg h]

theorem submission.h1 : @EquationLHS Int submission.M := by
  intro x y
  show x = submission.op (submission.op x y)
        (submission.op (submission.op x y) y)
  by_cases h : y < x
  · have a1 := submission.op_gt x y h
    rw [a1]
    have a2 := submission.op_gt (x + 1) y (by omega)
    rw [a2]
    have a3 := submission.op_le (x + 1) (x + 2) (by omega)
    rw [a3]
    omega
  · have a1 := submission.op_le x y h
    rw [a1]
    have a2 := submission.op_le (x - 1) y (by omega)
    rw [a2]
    have a3 := submission.op_gt (x - 1) (x - 2) (by omega)
    rw [a3]
    omega

theorem submission.h2 : ¬ @EquationRHS Int submission.M := by
  intro h
  exact absurd (h ((-10) : Int)) (by decide)

def submission : Goal :=
  ⟨Int, submission.M, submission.h1, submission.h2⟩
