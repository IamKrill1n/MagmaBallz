import JudgeProblem

-- ETP model Equation1661 (thang chẵn lẻ có vùng vá 0..3), chiều DUAL (op đảo đối số), giả thuyết eq1979 — tổ hợp op mở ra y hệt chiều gốc.
-- Base law eq1661: x = (x ◇ y) ◇ ((y ◇ z) ◇ y).
-- Bất biến then chốt: C := (y ◇ z) ◇ y luôn cùng chẵn lẻ với y, và mọi
-- nhánh của phép ghép cuối chỉ cần CHẴN LẺ của C, không cần giá trị.

def submission.op (x t : Nat) : Nat :=
  if x = 0 then (if t % 2 = 0 then 0 else 2)
  else if x = 1 then (if t % 2 = 0 then 1 else 3)
  else if x = 2 then (if t % 2 = 0 then 2 else 0)
  else if x = 3 then (if t % 2 = 0 then 4 else 1)
  else (if x % 2 = t % 2 then x - 1 else x + 1)

def submission.M : Magma Nat := { op := fun a b => submission.op b a }

theorem submission.op0 (t : Nat) :
    submission.op 0 t = if t % 2 = 0 then 0 else 2 := by
  simp [submission.op]

theorem submission.op1 (t : Nat) :
    submission.op 1 t = if t % 2 = 0 then 1 else 3 := by
  simp [submission.op]

theorem submission.op2 (t : Nat) :
    submission.op 2 t = if t % 2 = 0 then 2 else 0 := by
  simp [submission.op]

theorem submission.op3 (t : Nat) :
    submission.op 3 t = if t % 2 = 0 then 4 else 1 := by
  simp [submission.op]

theorem submission.opg_eq (x t : Nat) (hx : 4 ≤ x) (h : x % 2 = t % 2) :
    submission.op x t = x - 1 := by
  simp only [submission.op]
  rw [if_neg (by omega : ¬ x = 0), if_neg (by omega : ¬ x = 1),
      if_neg (by omega : ¬ x = 2), if_neg (by omega : ¬ x = 3), if_pos h]

theorem submission.opg_ne (x t : Nat) (hx : 4 ≤ x) (h : ¬ x % 2 = t % 2) :
    submission.op x t = x + 1 := by
  simp only [submission.op]
  rw [if_neg (by omega : ¬ x = 0), if_neg (by omega : ¬ x = 1),
      if_neg (by omega : ¬ x = 2), if_neg (by omega : ¬ x = 3), if_neg h]

-- C = (y ◇ z) ◇ y cùng chẵn lẻ với y, với mọi y z.
theorem submission.cpar (y z : Nat) :
    submission.op (submission.op y z) y % 2 = y % 2 := by
  by_cases h0 : y = 0
  · subst h0
    by_cases hz : z % 2 = 0
    · rw [submission.op0 z, if_pos hz, submission.op0 0, if_pos rfl]
    · rw [submission.op0 z, if_neg hz, submission.op2 0, if_pos rfl]
  · by_cases h1 : y = 1
    · subst h1
      by_cases hz : z % 2 = 0
      · rw [submission.op1 z, if_pos hz, submission.op1 1,
            if_neg (by omega : ¬ (1 : Nat) % 2 = 0)]
      · rw [submission.op1 z, if_neg hz, submission.op3 1,
            if_neg (by omega : ¬ (1 : Nat) % 2 = 0)]
    · by_cases h2 : y = 2
      · subst h2
        by_cases hz : z % 2 = 0
        · rw [submission.op2 z, if_pos hz, submission.op2 2,
              if_pos (by omega : (2 : Nat) % 2 = 0)]
        · rw [submission.op2 z, if_neg hz, submission.op0 2,
              if_pos (by omega : (2 : Nat) % 2 = 0)]
      · by_cases h3 : y = 3
        · subst h3
          by_cases hz : z % 2 = 0
          · rw [submission.op3 z, if_pos hz]
            have hb := submission.opg_ne 4 3 (by omega) (by omega)
            omega
          · rw [submission.op3 z, if_neg hz, submission.op1 3,
                if_neg (by omega : ¬ (3 : Nat) % 2 = 0)]
        · have hy4 : 4 ≤ y := by omega
          by_cases hz : y % 2 = z % 2
          · rw [submission.opg_eq y z hy4 hz]
            by_cases hy5 : y = 4
            · subst hy5
              show submission.op 3 4 % 2 = 4 % 2
              rw [submission.op3 4, if_pos (by omega : (4 : Nat) % 2 = 0)]
            · have hc := submission.opg_ne (y - 1) y (by omega) (by omega)
              omega
          · rw [submission.opg_ne y z hy4 hz]
            have hc := submission.opg_ne (y + 1) y (by omega) (by omega)
            omega

theorem submission.h1 : @EquationLHS Nat submission.M := by
  intro x y z
  show x = submission.op (submission.op x y)
        (submission.op (submission.op y z) y)
  generalize hg : submission.op (submission.op y z) y = C
  have hC : C % 2 = y % 2 := by
    rw [← hg]
    exact submission.cpar y z
  by_cases hy : y % 2 = 0
  · by_cases h0 : x = 0
    · subst h0
      rw [submission.op0 y, if_pos hy, submission.op0 C,
          if_pos (by omega : C % 2 = 0)]
    · by_cases h1 : x = 1
      · subst h1
        rw [submission.op1 y, if_pos hy, submission.op1 C,
            if_pos (by omega : C % 2 = 0)]
      · by_cases h2 : x = 2
        · subst h2
          rw [submission.op2 y, if_pos hy, submission.op2 C,
              if_pos (by omega : C % 2 = 0)]
        · by_cases h3 : x = 3
          · subst h3
            rw [submission.op3 y, if_pos hy]
            have hf := submission.opg_eq 4 C (by omega) (by omega)
            omega
          · have hx4 : 4 ≤ x := by omega
            by_cases hxy : x % 2 = y % 2
            · rw [submission.opg_eq x y hx4 hxy]
              by_cases hx5 : x = 4
              · subst hx5
                show (4 : Nat) = submission.op 3 C
                rw [submission.op3 C, if_pos (by omega : C % 2 = 0)]
              · have hf := submission.opg_ne (x - 1) C (by omega) (by omega)
                omega
            · rw [submission.opg_ne x y hx4 hxy]
              have hf := submission.opg_eq (x + 1) C (by omega) (by omega)
              omega
  · by_cases h0 : x = 0
    · subst h0
      rw [submission.op0 y, if_neg hy, submission.op2 C,
          if_neg (by omega : ¬ C % 2 = 0)]
    · by_cases h1 : x = 1
      · subst h1
        rw [submission.op1 y, if_neg hy, submission.op3 C,
            if_neg (by omega : ¬ C % 2 = 0)]
      · by_cases h2 : x = 2
        · subst h2
          rw [submission.op2 y, if_neg hy, submission.op0 C,
              if_neg (by omega : ¬ C % 2 = 0)]
        · by_cases h3 : x = 3
          · subst h3
            rw [submission.op3 y, if_neg hy, submission.op1 C,
                if_neg (by omega : ¬ C % 2 = 0)]
          · have hx4 : 4 ≤ x := by omega
            by_cases hxy : x % 2 = y % 2
            · rw [submission.opg_eq x y hx4 hxy]
              have hf := submission.opg_ne (x - 1) C (by omega) (by omega)
              omega
            · rw [submission.opg_ne x y hx4 hxy]
              have hf := submission.opg_eq (x + 1) C (by omega) (by omega)
              omega

theorem submission.h2 : ¬ @EquationRHS Nat submission.M := by
  intro h
  exact absurd (h {VIOLATION}) (by decide)

def submission : Goal :=
  ⟨Nat, submission.M, submission.h1, submission.h2⟩
