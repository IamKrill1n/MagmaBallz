import JudgeProblem

def submission : Goal := by
  intro G _ h0
  have h1 : ∀ x y z w u : G, x = ((y ◇ z) ◇ (w ◇ (u ◇ x))) := by
    have h := h0
    exact h
  exact h1
