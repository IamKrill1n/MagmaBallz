import JudgeProblem

def submission : Goal := by
  intro G _ h0
  have h1 : ∀ x y : G, x = (y ◇ ((x ◇ x) ◇ x)) := by
    have h := h0
    have lem1 : ∀ x y : G, x = (((y ◇ x) ◇ y) ◇ x) := by
      intro x y
      exact (h x (x ◇ ((x ◇ ((y ◇ x) ◇ y)) ◇ x)) y).trans (congrArg (fun t => (t ◇ x)) ((h ((y ◇ x) ◇ y) x x).symm))
    have lem2 : ∀ x y z : G, ((x ◇ y) ◇ x) = ((z ◇ y) ◇ ((x ◇ y) ◇ x)) := by
      intro x y z
      exact (h ((x ◇ y) ◇ x) z y).trans (congrArg (fun t => ((z ◇ t) ◇ ((x ◇ y) ◇ x))) ((h y y x).symm))
    have lem4 : ∀ x y z w u : G, x = ((y ◇ (((z ◇ ((w ◇ (u ◇ x)) ◇ w)) ◇ (u ◇ x)) ◇ u)) ◇ x) := by
      intro x y z w u
      exact (h x y u).trans (congrArg (fun t => ((y ◇ (t ◇ u)) ◇ x)) (h (u ◇ x) z w))
    have lem13 : ∀ x y z : G, x = (((((y ◇ (z ◇ x)) ◇ y) ◇ (z ◇ x)) ◇ z) ◇ x) := by
      intro x y z
      exact (lem1 x z).trans (congrArg (fun t => ((t ◇ z) ◇ x)) (lem1 (z ◇ x) y))
    have lem20 : ∀ x y z w : G, x = ((((y ◇ ((z ◇ (w ◇ x)) ◇ z)) ◇ (w ◇ x)) ◇ w) ◇ x) := by
      intro x y z w
      exact (lem4 x ((x ◇ (((y ◇ ((z ◇ (w ◇ x)) ◇ z)) ◇ (w ◇ x)) ◇ w)) ◇ x) y z w).trans (congrArg (fun t => (t ◇ x)) ((lem1 (((y ◇ ((z ◇ (w ◇ x)) ◇ z)) ◇ (w ◇ x)) ◇ w) x).symm))
    have lem29 : ∀ x y z : G, ((x ◇ y) ◇ x) = ((((x ◇ y) ◇ x) ◇ (z ◇ y)) ◇ ((x ◇ y) ◇ x)) := by
      intro x y z
      exact (lem1 ((x ◇ y) ◇ x) (z ◇ y)).trans (congrArg (fun t => ((t ◇ (z ◇ y)) ◇ ((x ◇ y) ◇ x))) ((lem2 x y z).symm))
    have lem30 : ∀ x y z w : G, ((x ◇ y) ◇ x) = (((z ◇ w) ◇ ((y ◇ w) ◇ y)) ◇ ((x ◇ y) ◇ x)) := by
      intro x y z w
      exact (lem2 x y (y ◇ w)).trans (congrArg (fun t => (t ◇ ((x ◇ y) ◇ x))) (lem2 y w z))
    have lem34 : ∀ x y : G, x = ((((x ◇ y) ◇ x) ◇ (x ◇ y)) ◇ x) := by
      intro x y
      exact (lem20 x (x ◇ ((x ◇ y) ◇ x)) y (x ◇ y)).trans (congrArg (fun t => ((t ◇ (x ◇ y)) ◇ x)) ((lem30 x y x ((x ◇ y) ◇ x)).symm))
    have lem38 : ∀ x y z : G, x = (((((y ◇ x) ◇ y) ◇ (z ◇ x)) ◇ z) ◇ x) := by
      intro x y z
      exact (lem13 x ((y ◇ x) ◇ y) z).trans (congrArg (fun t => (((t ◇ (z ◇ x)) ◇ z) ◇ x)) ((lem29 y x z).symm))
    have lem58 : ∀ x y : G, x = (y ◇ x) := by
      intro x y
      exact (lem38 x y y).trans (congrArg (fun t => (t ◇ x)) ((lem34 y x).symm))
    have lem84 : ∀ x y z : G, x = (y ◇ (z ◇ x)) := by
      intro x y z
      exact (lem58 x z).trans (lem58 (z ◇ x) y)
    intro x y
    exact lem84 x y (x ◇ x)
  have h2 : ∀ x y z w : G, x = (((y ◇ z) ◇ w) ◇ (w ◇ x)) := by
    have h := h1
    have lem1 : ∀ x y : G, ((x ◇ x) ◇ x) = (y ◇ x) := by
      intro x y
      exact (h ((x ◇ x) ◇ x) y).trans (congrArg (fun t => (y ◇ t)) ((h x (((x ◇ x) ◇ x) ◇ ((x ◇ x) ◇ x))).symm))
    have lem7 : ∀ x y z : G, x = (y ◇ (z ◇ x)) := by
      intro x y z
      exact (h x y).trans (congrArg (fun t => (y ◇ t)) (lem1 x z))
    intro x y z w
    exact lem7 x ((y ◇ z) ◇ w) w
  exact h2
