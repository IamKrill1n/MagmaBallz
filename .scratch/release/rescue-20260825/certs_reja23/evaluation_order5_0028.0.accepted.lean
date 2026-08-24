import JudgeProblem

set_option maxHeartbeats 12800000 in
def submission : Goal := by
  intro G _ h
  have proj_l : ∀ a b : G, (a ◇ b) = a := by
    intro a b
    have E1 : ∀ (v0 v1 v2 : G), (v0 ◇ v1) = v0 := by intro v0 v1 v2; have ia := h v0 v1 ((((v2 ◇ v2) ◇ v2) ◇ v2)); have ib := h v1 ((((((v2 ◇ v2) ◇ v2) ◇ v2) ◇ (((v2 ◇ v2) ◇ v2) ◇ v2)) ◇ (((v2 ◇ v2) ◇ v2) ◇ v2))) v2; have step : (v0 ◇ (v1 ◇ ((((((v2 ◇ v2) ◇ v2) ◇ v2) ◇ (((v2 ◇ v2) ◇ v2) ◇ v2)) ◇ (((v2 ◇ v2) ◇ v2) ◇ v2)) ◇ (((v2 ◇ v2) ◇ v2) ◇ v2)))) = (v0 ◇ v1) := congrArg (fun __pc_hole => (v0 ◇ __pc_hole)) ((ib).symm); exact step.symm.trans ((ia).symm)
    have target : ∀ (v0 v1 : G), (v0 ◇ v1) = v0 := fun v0 v1 => E1 v0 v1 v0
    exact target a b
  intro x y
  exact (proj_l x ((((x ◇ y) ◇ x) ◇ (x ◇ y)))).symm
