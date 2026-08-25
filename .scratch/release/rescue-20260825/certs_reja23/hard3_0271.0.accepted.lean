import JudgeProblem

set_option maxHeartbeats 12800000 in
def submission : Goal := by
  intro G _ h
  have proj_r : ∀ a b : G, (a ◇ b) = b := by
    intro a b
    have E2 : ∀ (v0 v1 v2 v3 : G), (((v0 ◇ v1) ◇ v0) ◇ v1) = v1 := by intro v0 v1 v2 v3; have ia := h v1 ((v2 ◇ ((v3 ◇ ((v0 ◇ v1) ◇ v0)) ◇ v3))) v0; have ib := h (((v0 ◇ v1) ◇ v0)) v2 v3; have step : (((v2 ◇ ((v3 ◇ ((v0 ◇ v1) ◇ v0)) ◇ v3)) ◇ ((v0 ◇ v1) ◇ v0)) ◇ v1) = (((v0 ◇ v1) ◇ v0) ◇ v1) := congrArg (fun __pc_hole => (__pc_hole ◇ v1)) ((ib).symm); exact step.symm.trans ((ia).symm)
    have E21 : ∀ (v0 v1 v2 v3 v4 v5 v6 : G), (((((v0 ◇ (v1 ◇ v2)) ◇ v0) ◇ (v1 ◇ v2)) ◇ v1) ◇ v2) = v2 := by intro v0 v1 v2 v3 v4 v5 v6; have ia := E2 v1 v2 v3 v4; have ib := E2 v0 ((v1 ◇ v2)) v5 v6; have step : (((v1 ◇ v2) ◇ v1) ◇ v2) = (((((v0 ◇ (v1 ◇ v2)) ◇ v0) ◇ (v1 ◇ v2)) ◇ v1) ◇ v2) := congrArg (fun __pc_hole => ((__pc_hole ◇ v1) ◇ v2)) ((ib).symm); exact step.symm.trans (ia)
    have E3 : ∀ (v0 v1 v2 : G), ((v0 ◇ v1) ◇ ((v2 ◇ v1) ◇ v2)) = ((v2 ◇ v1) ◇ v2) := by intro v0 v1 v2; have ia := h (((v2 ◇ v1) ◇ v2)) v0 v1; have ib := h v1 v1 v2; have step : ((v0 ◇ ((v1 ◇ ((v2 ◇ v1) ◇ v2)) ◇ v1)) ◇ ((v2 ◇ v1) ◇ v2)) = ((v0 ◇ v1) ◇ ((v2 ◇ v1) ◇ v2)) := congrArg (fun __pc_hole => ((v0 ◇ __pc_hole) ◇ ((v2 ◇ v1) ◇ v2))) ((ib).symm); exact step.symm.trans ((ia).symm)
    have E22 : ∀ (v0 v1 v2 v3 v4 : G), ((((v0 ◇ v1) ◇ v0) ◇ (v2 ◇ v1)) ◇ ((v0 ◇ v1) ◇ v0)) = ((v0 ◇ v1) ◇ v0) := by intro v0 v1 v2 v3 v4; have ia := E2 ((v2 ◇ v1)) (((v0 ◇ v1) ◇ v0)) v3 v4; have ib := E3 v2 v1 v0; have step : ((((v2 ◇ v1) ◇ ((v0 ◇ v1) ◇ v0)) ◇ (v2 ◇ v1)) ◇ ((v0 ◇ v1) ◇ v0)) = ((((v0 ◇ v1) ◇ v0) ◇ (v2 ◇ v1)) ◇ ((v0 ◇ v1) ◇ v0)) := congrArg (fun __pc_hole => ((__pc_hole ◇ (v2 ◇ v1)) ◇ ((v0 ◇ v1) ◇ v0))) (ib); exact step.symm.trans (ia)
    have E208 : ∀ (v0 v1 v2 v3 v4 v5 v6 v7 v8 : G), (((((v0 ◇ v1) ◇ v0) ◇ (v2 ◇ v1)) ◇ v2) ◇ v1) = v1 := by intro v0 v1 v2 v3 v4 v5 v6 v7 v8; have ia := E21 (((v0 ◇ v1) ◇ v0)) v2 v1 v3 v4 v5 v6; have ib := E22 v0 v1 v2 v7 v8; have step : (((((((v0 ◇ v1) ◇ v0) ◇ (v2 ◇ v1)) ◇ ((v0 ◇ v1) ◇ v0)) ◇ (v2 ◇ v1)) ◇ v2) ◇ v1) = (((((v0 ◇ v1) ◇ v0) ◇ (v2 ◇ v1)) ◇ v2) ◇ v1) := congrArg (fun __pc_hole => (((__pc_hole ◇ (v2 ◇ v1)) ◇ v2) ◇ v1)) (ib); exact step.symm.trans (ia)
    have E569 : ∀ (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : G), (v0 ◇ v1) = v1 := by intro v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11; have ia := E21 (((v0 ◇ v1) ◇ v0)) v0 v1 v2 v3 v4 v5; have ib := E208 ((v0 ◇ v1)) v0 ((v0 ◇ v1)) v6 v7 v8 v9 v10 v11; have step : (((((((v0 ◇ v1) ◇ v0) ◇ (v0 ◇ v1)) ◇ ((v0 ◇ v1) ◇ v0)) ◇ (v0 ◇ v1)) ◇ v0) ◇ v1) = (v0 ◇ v1) := congrArg (fun __pc_hole => (__pc_hole ◇ v1)) (ib); exact step.symm.trans (ia)
    have target : ∀ (v0 v1 : G), (v0 ◇ v1) = v1 := fun v0 v1 => E569 v0 v1 v0 v0 v0 v0 v0 v0 v0 v0 v0 v0
    exact target a b
  intro x y z w
  calc
    x = (w ◇ x) := (proj_r w x).symm
    _ = (((y ◇ z) ◇ w) ◇ (w ◇ x)) := (proj_r (((y ◇ z) ◇ w)) ((w ◇ x))).symm
