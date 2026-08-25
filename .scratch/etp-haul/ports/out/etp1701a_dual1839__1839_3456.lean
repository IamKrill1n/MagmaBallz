import JudgeProblem

-- [DUAL, luật nền eq1839] ETP model op_1701_8: op a b = if b = 0 then 0 else (b-1 / b+1 theo chẵn lẻ).
-- Base law eq1701: x = (y ◇ x) ◇ ((z ◇ x) ◇ x).

def submission.op (a b : Nat) : Nat :=
  if b = 0 then 0 else (if a % 2 = b % 2 then b - 1 else b + 1)

def submission.M : Magma Nat := { op := fun a b => submission.op b a }

theorem submission.op_z (a : Nat) : submission.op a 0 = 0 := by
  simp [submission.op]

theorem submission.op_eq (a b : Nat) (hb : ¬ b = 0) (h : a % 2 = b % 2) :
    submission.op a b = b - 1 := by
  simp only [submission.op]
  rw [if_neg hb, if_pos h]

theorem submission.op_ne (a b : Nat) (hb : ¬ b = 0) (h : ¬ a % 2 = b % 2) :
    submission.op a b = b + 1 := by
  simp only [submission.op]
  rw [if_neg hb, if_neg h]

theorem submission.op_par (a b : Nat) (hb : ¬ b = 0) :
    ¬ submission.op a b % 2 = b % 2 := by
  by_cases h : a % 2 = b % 2
  · have he := submission.op_eq a b hb h
    omega
  · have he := submission.op_ne a b hb h
    omega

theorem submission.h1 : @EquationLHS Nat submission.M := by
  intro x y z
  show x = submission.op (submission.op z x)
        (submission.op (submission.op y x) x)
  by_cases hx : x = 0
  · subst hx
    rfl
  · have hC := submission.op_ne (submission.op y x) x hx
      (submission.op_par y x hx)
    by_cases hy : z % 2 = x % 2
    · have hA := submission.op_eq z x hx hy
      rw [hA, hC]
      have hf := submission.op_eq (x - 1) (x + 1) (by omega) (by omega)
      rw [hf]
      omega
    · have hA := submission.op_ne z x hx hy
      rw [hA, hC]
      have hf := submission.op_eq (x + 1) (x + 1) (by omega) rfl
      rw [hf]
      omega

theorem submission.h2 : ¬ @EquationRHS Nat submission.M := by
  intro h
  exact absurd (h 1) (by decide)

def submission : Goal :=
  ⟨Nat, submission.M, submission.h1, submission.h2⟩
