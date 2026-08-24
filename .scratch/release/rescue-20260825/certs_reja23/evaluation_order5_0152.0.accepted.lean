import JudgeProblem

set_option maxHeartbeats 12800000 in
def submission : Goal := by
  intro G _ h
  have proj_r : ∀ a b : G, (a ◇ b) = b := by
    intro a b
    have E2 : ∀ (v0 v1 v2 v3 v4 : G), ((((v0 ◇ v1) ◇ ((v0 ◇ v0) ◇ v1)) ◇ ((v2 ◇ v3) ◇ ((v2 ◇ v2) ◇ v3))) ◇ v4) = v4 := by intro v0 v1 v2 v3 v4; have ia := h v4 v2 v3; have ib := h (((v2 ◇ v3) ◇ ((v2 ◇ v2) ◇ v3))) v0 v1; have step : (((v2 ◇ v3) ◇ ((v2 ◇ v2) ◇ v3)) ◇ v4) = ((((v0 ◇ v1) ◇ ((v0 ◇ v0) ◇ v1)) ◇ ((v2 ◇ v3) ◇ ((v2 ◇ v2) ◇ v3))) ◇ v4) := congrArg (fun __pc_hole => (__pc_hole ◇ v4)) (ib); exact step.symm.trans ((ia).symm)
    have E7 : ∀ (v0 v1 v2 v3 : G), (((((v0 ◇ v1) ◇ ((v0 ◇ v0) ◇ v1)) ◇ v2) ◇ v2) ◇ v3) = v3 := by intro v0 v1 v2 v3; have ia := h v3 (((v0 ◇ v1) ◇ ((v0 ◇ v0) ◇ v1))) v2; have ib := E2 v0 v1 v0 v1 v2; have step : (((((v0 ◇ v1) ◇ ((v0 ◇ v0) ◇ v1)) ◇ v2) ◇ ((((v0 ◇ v1) ◇ ((v0 ◇ v0) ◇ v1)) ◇ ((v0 ◇ v1) ◇ ((v0 ◇ v0) ◇ v1))) ◇ v2)) ◇ v3) = (((((v0 ◇ v1) ◇ ((v0 ◇ v0) ◇ v1)) ◇ v2) ◇ v2) ◇ v3) := congrArg (fun __pc_hole => (((((v0 ◇ v1) ◇ ((v0 ◇ v0) ◇ v1)) ◇ v2) ◇ __pc_hole) ◇ v3)) (ib); exact step.symm.trans ((ia).symm)
    have E9 : ∀ (v0 v1 v2 v3 : G), ((v0 ◇ v0) ◇ v1) = v1 := by intro v0 v1 v2 v3; have ia := E7 v2 v3 v0 v1; have ib := h v0 v2 v3; have step : (((((v2 ◇ v3) ◇ ((v2 ◇ v2) ◇ v3)) ◇ v0) ◇ v0) ◇ v1) = ((v0 ◇ v0) ◇ v1) := congrArg (fun __pc_hole => ((__pc_hole ◇ v0) ◇ v1)) ((ib).symm); exact step.symm.trans (ia)
    have E71 : ∀ (v0 v1 v2 v3 v4 v5 v6 : G), (((((v0 ◇ v1) ◇ ((v0 ◇ v0) ◇ v1)) ◇ v2) ◇ v2) ◇ ((v3 ◇ v3) ◇ v4)) = v4 := by intro v0 v1 v2 v3 v4 v5 v6; have ia := E9 v3 v4 v5 v6; have ib := E7 v0 v1 v2 (((v3 ◇ v3) ◇ v4)); have step : ((v3 ◇ v3) ◇ v4) = (((((v0 ◇ v1) ◇ ((v0 ◇ v0) ◇ v1)) ◇ v2) ◇ v2) ◇ ((v3 ◇ v3) ◇ v4)) := congrArg (fun __pc_hole => __pc_hole) ((ib).symm); exact step.symm.trans (ia)
    have E154 : ∀ (v0 v1 v2 v3 v4 v5 : G), (v0 ◇ v1) = v1 := by intro v0 v1 v2 v3 v4 v5; have ia := h v1 ((((v2 ◇ v3) ◇ ((v2 ◇ v2) ◇ v3)) ◇ v0)) v0; have ib := E71 v2 v3 v0 ((((v2 ◇ v3) ◇ ((v2 ◇ v2) ◇ v3)) ◇ v0)) v0 v4 v5; have step : ((((((v2 ◇ v3) ◇ ((v2 ◇ v2) ◇ v3)) ◇ v0) ◇ v0) ◇ (((((v2 ◇ v3) ◇ ((v2 ◇ v2) ◇ v3)) ◇ v0) ◇ (((v2 ◇ v3) ◇ ((v2 ◇ v2) ◇ v3)) ◇ v0)) ◇ v0)) ◇ v1) = (v0 ◇ v1) := congrArg (fun __pc_hole => (__pc_hole ◇ v1)) (ib); exact step.symm.trans ((ia).symm)
    have target : ∀ (v0 v1 : G), (v0 ◇ v1) = v1 := fun v0 v1 => E154 v0 v1 v0 v0 v0 v0
    exact target a b
  intro x y z
  have f97 := proj_r (z ◇ (x ◇ y)) x
  have f54 := proj_r x ((z ◇ (x ◇ y)) ◇ x)
  have f61 := proj_r y (x ◇ ((z ◇ (x ◇ y)) ◇ x))
  calc
    x = ((z ◇ (x ◇ y)) ◇ x) := by simpa using f97.symm
    _ = (x ◇ ((z ◇ (x ◇ y)) ◇ x)) := by simpa using f54.symm
    _ = (y ◇ (x ◇ ((z ◇ (x ◇ y)) ◇ x))) := by simpa using f61.symm
