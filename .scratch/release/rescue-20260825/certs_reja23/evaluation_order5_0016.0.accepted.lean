import JudgeProblem

set_option maxHeartbeats 12800000 in
def submission : Goal := by
  intro G _ h
  have const : ∀ a b : G, a = b := by
    intro a b
    have E1 : ∀ (v0 v1 v2 v3 : G), (v0 ◇ ((v1 ◇ ((v2 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3))) ◇ v2)) = v1 := by intro v0 v1 v2 v3; have ia := h v1 v0 (((v2 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3))); have ib := h v2 ((((v2 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3)) ◇ ((v2 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3)))) v3; have step : (v0 ◇ ((v1 ◇ ((v2 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3))) ◇ ((((v2 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3)) ◇ ((v2 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3))) ◇ ((v2 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3))))) = (v0 ◇ ((v1 ◇ ((v2 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3))) ◇ v2)) := congrArg (fun __pc_hole => (v0 ◇ ((v1 ◇ ((v2 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3))) ◇ __pc_hole))) ((ib).symm); exact step.symm.trans ((ia).symm)
    have E2 : ∀ (v0 v1 v2 v3 v4 : G), (v0 ◇ v1) = v2 := by intro v0 v1 v2 v3 v4; have ia := E1 v0 v2 (((v1 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3))) v4; have ib := h v1 ((v2 ◇ ((((v1 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3)) ◇ v4) ◇ ((v4 ◇ v4) ◇ v4)))) v3; have step : (v0 ◇ ((v2 ◇ ((((v1 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3)) ◇ v4) ◇ ((v4 ◇ v4) ◇ v4))) ◇ ((v1 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3)))) = (v0 ◇ v1) := congrArg (fun __pc_hole => (v0 ◇ __pc_hole)) ((ib).symm); exact step.symm.trans (ia)
    have E4 : ∀ (v0 v1 v2 v3 v4 v5 : G), v0 = v1 := by intro v0 v1 v2 v3 v4 v5; have ia := h v1 v2 v3; have ib := E2 v2 (((v1 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3))) v0 v4 v5; have step : (v2 ◇ ((v1 ◇ v3) ◇ ((v3 ◇ v3) ◇ v3))) = v0 := congrArg (fun __pc_hole => __pc_hole) (ib); exact step.symm.trans ((ia).symm)
    have target : ∀ (v0 v1 : G), v0 = v1 := fun v0 v1 => E4 v0 v1 v0 v0 v0 v0
    exact target a b
  intro x y z w u
  exact const x ((y ◇ z) ◇ (y ◇ (w ◇ (w ◇ u))))
