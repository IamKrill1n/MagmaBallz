import JudgeProblem

-- [DUAL, luật nền eq2000] ETP model Equation1659, chiều GỐC (không đảo đối số).
-- Base law eq1659: x = (x ◇ y) ◇ ((y ◇ y) ◇ z).
-- Cùng op với cert 1167 (dual) đã accepted; khác phần lắp h1.

def submission.op (x t : Nat) : Nat :=
  if x = 0 then (if t % 2 = 0 then 1 else 0)
  else (if x % 2 = t % 2 then x + 1 else x - 1)

def submission.M : Magma Nat := { op := fun a b => submission.op b a }

theorem submission.op_pos_eq (x t : Nat) (hx : ¬ x = 0) (h : x % 2 = t % 2) :
    submission.op x t = x + 1 := by
  simp only [submission.op]
  rw [if_neg hx, if_pos h]

theorem submission.op_pos_ne (x t : Nat) (hx : ¬ x = 0) (h : ¬ x % 2 = t % 2) :
    submission.op x t = x - 1 := by
  simp only [submission.op]
  rw [if_neg hx, if_neg h]

theorem submission.op_zero (t : Nat) :
    submission.op 0 t = if t % 2 = 0 then 1 else 0 := by
  simp [submission.op]

theorem submission.op_self (y : Nat) : submission.op y y = y + 1 := by
  by_cases hy : y = 0
  · subst hy
    rw [submission.op_zero 0, if_pos rfl]
  · exact submission.op_pos_eq y y hy rfl

theorem submission.op_pos_mod (x z : Nat) (hx : ¬ x = 0) :
    submission.op x z % 2 = (x + 1) % 2 := by
  by_cases h : x % 2 = z % 2
  · have he := submission.op_pos_eq x z hx h
    omega
  · have he := submission.op_pos_ne x z hx h
    omega

theorem submission.h1 : @EquationLHS Nat submission.M := by
  intro x y z
  show x = submission.op (submission.op x z)
        (submission.op (submission.op z z) y)
  rw [submission.op_self z]
  generalize hg : submission.op (z + 1) y = B
  have hB : B % 2 = (z + 1 + 1) % 2 := by
    rw [← hg]
    exact submission.op_pos_mod (z + 1) y (by omega)
  by_cases hx : x = 0
  · subst hx
    by_cases hy : z % 2 = 0
    · rw [submission.op_zero z, if_pos hy]
      have hf := submission.op_pos_ne 1 B (by omega) (by omega)
      rw [hf]
    · rw [submission.op_zero z, if_neg hy]
      rw [submission.op_zero B, if_neg (show ¬ B % 2 = 0 by omega)]
  · by_cases hxy : x % 2 = z % 2
    · rw [submission.op_pos_eq x z hx hxy]
      have hf := submission.op_pos_ne (x + 1) B (by omega) (by omega)
      rw [hf]
      omega
    · rw [submission.op_pos_ne x z hx hxy]
      by_cases hx1 : x = 1
      · subst hx1
        show 1 = submission.op 0 B
        rw [submission.op_zero B, if_pos (show B % 2 = 0 by omega)]
      · have hf := submission.op_pos_eq (x - 1) B (by omega) (by omega)
        rw [hf]
        omega

theorem submission.h2 : ¬ @EquationRHS Nat submission.M := by
  intro h
  exact absurd (h 1 0) (by decide)

def submission : Goal :=
  ⟨Nat, submission.M, submission.h1, submission.h2⟩
