import JudgeProblem

set_option maxHeartbeats 12800000 in
def submission : Goal := by
  intro G _ h
  have proj_l : ∀ a b : G, (a ◇ b) = a := by
    intro a b
    have E3 : ∀ (v0 v1 v2 v3 : G), (v0 ◇ (v1 ◇ (v0 ◇ v1))) = v0 := by intro v0 v1 v2 v3; have ia := h v0 v1 (((v2 ◇ v3) ◇ (v1 ◇ v2))); have ib := h v1 v2 v3; have step : (v0 ◇ ((v1 ◇ ((v2 ◇ v3) ◇ (v1 ◇ v2))) ◇ (v0 ◇ v1))) = (v0 ◇ (v1 ◇ (v0 ◇ v1))) := congrArg (fun __pc_hole => (v0 ◇ (__pc_hole ◇ (v0 ◇ v1)))) ((ib).symm); exact step.symm.trans ((ia).symm)
    have E15 : ∀ (v0 v1 v2 v3 v4 v5 v6 : G), (v0 ◇ (v1 ◇ ((v0 ◇ v1) ◇ (v2 ◇ ((v0 ◇ v1) ◇ v2))))) = v0 := by intro v0 v1 v2 v3 v4 v5 v6; have ia := E3 v0 v1 v3 v4; have ib := E3 ((v0 ◇ v1)) v2 v5 v6; have step : (v0 ◇ (v1 ◇ (v0 ◇ v1))) = (v0 ◇ (v1 ◇ ((v0 ◇ v1) ◇ (v2 ◇ ((v0 ◇ v1) ◇ v2))))) := congrArg (fun __pc_hole => (v0 ◇ (v1 ◇ __pc_hole))) ((ib).symm); exact step.symm.trans (ia)
    have E5 : ∀ (v0 v1 v2 v3 v4 : G), (v0 ◇ (((v1 ◇ (v0 ◇ v1)) ◇ v2) ◇ v0)) = v0 := by intro v0 v1 v2 v3 v4; have ia := h v0 ((v1 ◇ (v0 ◇ v1))) v2; have ib := E3 v0 v1 v3 v4; have step : (v0 ◇ (((v1 ◇ (v0 ◇ v1)) ◇ v2) ◇ (v0 ◇ (v1 ◇ (v0 ◇ v1))))) = (v0 ◇ (((v1 ◇ (v0 ◇ v1)) ◇ v2) ◇ v0)) := congrArg (fun __pc_hole => (v0 ◇ (((v1 ◇ (v0 ◇ v1)) ◇ v2) ◇ __pc_hole))) (ib); exact step.symm.trans ((ia).symm)
    have E12 : ∀ (v0 v1 v2 v3 v4 v5 : G), (v0 ◇ ((v1 ◇ (v0 ◇ v1)) ◇ v0)) = v0 := by intro v0 v1 v2 v3 v4 v5; have ia := E3 v0 ((v1 ◇ (v0 ◇ v1))) v2 v3; have ib := E3 v0 v1 v4 v5; have step : (v0 ◇ ((v1 ◇ (v0 ◇ v1)) ◇ (v0 ◇ (v1 ◇ (v0 ◇ v1))))) = (v0 ◇ ((v1 ◇ (v0 ◇ v1)) ◇ v0)) := congrArg (fun __pc_hole => (v0 ◇ ((v1 ◇ (v0 ◇ v1)) ◇ __pc_hole))) (ib); exact step.symm.trans (ia)
    have E49 : ∀ (v0 v1 v2 v3 v4 v5 v6 v7 v8 : G), ((v0 ◇ (v1 ◇ v0)) ◇ ((v1 ◇ v2) ◇ (v0 ◇ (v1 ◇ v0)))) = (v0 ◇ (v1 ◇ v0)) := by intro v0 v1 v2 v3 v4 v5 v6 v7 v8; have ia := E5 ((v0 ◇ (v1 ◇ v0))) v1 v2 v3 v4; have ib := E12 v1 v0 v5 v6 v7 v8; have step : ((v0 ◇ (v1 ◇ v0)) ◇ (((v1 ◇ ((v0 ◇ (v1 ◇ v0)) ◇ v1)) ◇ v2) ◇ (v0 ◇ (v1 ◇ v0)))) = ((v0 ◇ (v1 ◇ v0)) ◇ ((v1 ◇ v2) ◇ (v0 ◇ (v1 ◇ v0)))) := congrArg (fun __pc_hole => ((v0 ◇ (v1 ◇ v0)) ◇ ((__pc_hole ◇ v2) ◇ (v0 ◇ (v1 ◇ v0))))) (ib); exact step.symm.trans (ia)
    have E200 : ∀ (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : G), (v0 ◇ (v1 ◇ ((v0 ◇ v1) ◇ (v2 ◇ (v0 ◇ v2))))) = v0 := by intro v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12; have ia := E15 v0 v1 ((v2 ◇ (v0 ◇ v2))) v3 v4 v5 v6; have ib := E49 v2 v0 v1 v7 v8 v9 v10 v11 v12; have step : (v0 ◇ (v1 ◇ ((v0 ◇ v1) ◇ ((v2 ◇ (v0 ◇ v2)) ◇ ((v0 ◇ v1) ◇ (v2 ◇ (v0 ◇ v2))))))) = (v0 ◇ (v1 ◇ ((v0 ◇ v1) ◇ (v2 ◇ (v0 ◇ v2))))) := congrArg (fun __pc_hole => (v0 ◇ (v1 ◇ ((v0 ◇ v1) ◇ __pc_hole)))) (ib); exact step.symm.trans (ia)
    have E688 : ∀ (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : G), (v0 ◇ v1) = v0 := by intro v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15; have ia := E15 v0 v1 ((v1 ◇ (v0 ◇ v1))) v2 v3 v4 v5; have ib := E200 v1 ((v0 ◇ v1)) ((v0 ◇ v1)) v6 v7 v8 v9 v10 v11 v12 v13 v14 v15; have step : (v0 ◇ (v1 ◇ ((v0 ◇ v1) ◇ ((v1 ◇ (v0 ◇ v1)) ◇ ((v0 ◇ v1) ◇ (v1 ◇ (v0 ◇ v1))))))) = (v0 ◇ v1) := congrArg (fun __pc_hole => (v0 ◇ __pc_hole)) (ib); exact step.symm.trans (ia)
    have target : ∀ (v0 v1 : G), (v0 ◇ v1) = v0 := fun v0 v1 => E688 v0 v1 v0 v0 v0 v0 v0 v0 v0 v0 v0 v0 v0 v0 v0 v0
    exact target a b
  intro x y
  calc
    x = (x ◇ y) := (proj_l x y).symm
    _ = ((x ◇ y) ◇ (y ◇ y)) := (proj_l ((x ◇ y)) ((y ◇ y))).symm
