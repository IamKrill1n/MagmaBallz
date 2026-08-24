import JudgeProblem

set_option maxHeartbeats 12800000 in
def submission : Goal := by
  intro G _ h
  have square_overlap_bridge : ∀ x y : G, (((x ◇ x) ◇ y) ◇ (x ◇ y)) = (x ◇ (x ◇ x)) := by
    intro x y
    have E2 : ∀ (v0 v1 : G), (((v0 ◇ v0) ◇ v1) ◇ (v0 ◇ v1)) = (v0 ◇ (v0 ◇ v0)) := by intro v0 v1; have ia := h ((v0 ◇ (v0 ◇ v0))) ((v0 ◇ v0)) v1; have ib := h v0 v0 ((v0 ◇ v0)); have step : (((v0 ◇ v0) ◇ v1) ◇ (((v0 ◇ (v0 ◇ v0)) ◇ ((v0 ◇ (v0 ◇ v0)) ◇ (v0 ◇ v0))) ◇ v1)) = (((v0 ◇ v0) ◇ v1) ◇ (v0 ◇ v1)) := congrArg (fun __pc_hole => (((v0 ◇ v0) ◇ v1) ◇ (__pc_hole ◇ v1))) ((ib).symm); exact step.symm.trans ((ia).symm)
    have target : ∀ (v0 v1 : G), (((v0 ◇ v0) ◇ v1) ◇ (v0 ◇ v1)) = (v0 ◇ (v0 ◇ v0)) := fun v0 v1 => E2 v0 v1
    exact target x y
  have squares_equal : ∀ x y : G, (x ◇ x) = (y ◇ y) := by
    intro x y
    have E4 : ∀ (v0 v1 v2 v3 : G), (v0 ◇ ((v1 ◇ (v1 ◇ (v2 ◇ v3))) ◇ ((v0 ◇ (v0 ◇ v2)) ◇ v3))) = v1 := by intro v0 v1 v2 v3; have ia := h v1 ((v2 ◇ v3)) (((v0 ◇ (v0 ◇ v2)) ◇ v3)); have ib := h v0 v2 v3; have step : (((v2 ◇ v3) ◇ ((v0 ◇ (v0 ◇ v2)) ◇ v3)) ◇ ((v1 ◇ (v1 ◇ (v2 ◇ v3))) ◇ ((v0 ◇ (v0 ◇ v2)) ◇ v3))) = (v0 ◇ ((v1 ◇ (v1 ◇ (v2 ◇ v3))) ◇ ((v0 ◇ (v0 ◇ v2)) ◇ v3))) := congrArg (fun __pc_hole => (__pc_hole ◇ ((v1 ◇ (v1 ◇ (v2 ◇ v3))) ◇ ((v0 ◇ (v0 ◇ v2)) ◇ v3)))) ((ib).symm); exact step.symm.trans ((ia).symm)
    have E14 : ∀ (v0 v1 : G), (((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ (((v0 ◇ v0) ◇ v1) ◇ (v0 ◇ v1))) = (v0 ◇ (v0 ◇ v0)) := by intro v0 v1; have ia := square_overlap_bridge v0 ((v0 ◇ v0)); have ib := square_overlap_bridge v0 v1; have step : (((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ (v0 ◇ (v0 ◇ v0))) = (((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ (((v0 ◇ v0) ◇ v1) ◇ (v0 ◇ v1))) := congrArg (fun __pc_hole => (((v0 ◇ v0) ◇ (v0 ◇ v0)) ◇ __pc_hole)) ((ib).symm); exact step.symm.trans (ia)
    have E56 : ∀ (v0 v1 : G), (v0 ◇ ((v1 ◇ (v1 ◇ v1)) ◇ ((v0 ◇ (v0 ◇ v1)) ◇ (v1 ◇ v1)))) = ((v1 ◇ v1) ◇ (v1 ◇ v1)) := by intro v0 v1; have ia := E4 v0 (((v1 ◇ v1) ◇ (v1 ◇ v1))) v1 ((v1 ◇ v1)); have ib := E14 v1 ((v1 ◇ v1)); have step : (v0 ◇ ((((v1 ◇ v1) ◇ (v1 ◇ v1)) ◇ (((v1 ◇ v1) ◇ (v1 ◇ v1)) ◇ (v1 ◇ (v1 ◇ v1)))) ◇ ((v0 ◇ (v0 ◇ v1)) ◇ (v1 ◇ v1)))) = (v0 ◇ ((v1 ◇ (v1 ◇ v1)) ◇ ((v0 ◇ (v0 ◇ v1)) ◇ (v1 ◇ v1)))) := congrArg (fun __pc_hole => (v0 ◇ (__pc_hole ◇ ((v0 ◇ (v0 ◇ v1)) ◇ (v1 ◇ v1))))) (ib); exact step.symm.trans (ia)
    have E193 : ∀ (v0 v1 : G), (v0 ◇ v0) = ((v1 ◇ v1) ◇ (v1 ◇ v1)) := by intro v0 v1; have ia := E56 v0 v1; have ib := h v0 v1 ((v1 ◇ v1)); have step : (v0 ◇ ((v1 ◇ (v1 ◇ v1)) ◇ ((v0 ◇ (v0 ◇ v1)) ◇ (v1 ◇ v1)))) = (v0 ◇ v0) := congrArg (fun __pc_hole => (v0 ◇ __pc_hole)) ((ib).symm); exact step.symm.trans (ia)
    have E1056 : ∀ (v0 v1 v2 : G), (v0 ◇ v0) = (v1 ◇ v1) := by intro v0 v1 v2; have ia := E193 v1 v2; have ib := E193 v0 v2; have step : ((v2 ◇ v2) ◇ (v2 ◇ v2)) = (v0 ◇ v0) := congrArg (fun __pc_hole => __pc_hole) ((ib).symm); exact step.symm.trans ((ia).symm)
    have target : ∀ (v0 v1 : G), (v0 ◇ v0) = (v1 ◇ v1) := fun v0 v1 => E1056 v0 v1 v0
    exact target x y
  have square_left_identity : ∀ x y : G, ((x ◇ x) ◇ y) = y := by
    intro x y
    have E4 : ∀ (v0 v1 v2 : G), ((v0 ◇ v0) ◇ ((v1 ◇ (v1 ◇ v2)) ◇ v2)) = v1 := by intro v0 v1 v2; have ia := h v1 v2 v2; have ib := squares_equal v2 v0; have step : ((v2 ◇ v2) ◇ ((v1 ◇ (v1 ◇ v2)) ◇ v2)) = ((v0 ◇ v0) ◇ ((v1 ◇ (v1 ◇ v2)) ◇ v2)) := congrArg (fun __pc_hole => (__pc_hole ◇ ((v1 ◇ (v1 ◇ v2)) ◇ v2))) (ib); exact step.symm.trans ((ia).symm)
    have E5 : ∀ (v0 v1 v2 : G), ((v0 ◇ (v1 ◇ (v1 ◇ v0))) ◇ (v2 ◇ v2)) = v1 := by intro v0 v1 v2; have ia := h v1 v0 ((v1 ◇ (v1 ◇ v0))); have ib := squares_equal ((v1 ◇ (v1 ◇ v0))) v2; have step : ((v0 ◇ (v1 ◇ (v1 ◇ v0))) ◇ ((v1 ◇ (v1 ◇ v0)) ◇ (v1 ◇ (v1 ◇ v0)))) = ((v0 ◇ (v1 ◇ (v1 ◇ v0))) ◇ (v2 ◇ v2)) := congrArg (fun __pc_hole => ((v0 ◇ (v1 ◇ (v1 ◇ v0))) ◇ __pc_hole)) (ib); exact step.symm.trans ((ia).symm)
    have E19 : ∀ (v0 v1 : G), ((v0 ◇ v0) ◇ v1) = v1 := by intro v0 v1; have ia := E4 v0 v1 ((v1 ◇ v1)); have ib := E5 v1 v1 v1; have step : ((v0 ◇ v0) ◇ ((v1 ◇ (v1 ◇ (v1 ◇ v1))) ◇ (v1 ◇ v1))) = ((v0 ◇ v0) ◇ v1) := congrArg (fun __pc_hole => ((v0 ◇ v0) ◇ __pc_hole)) (ib); exact step.symm.trans (ia)
    have target : ∀ (v0 v1 : G), ((v0 ◇ v0) ◇ v1) = v1 := fun v0 v1 => E19 v0 v1
    exact target x y
  have t_cancellation : ∀ x y : G, ((x ◇ (x ◇ y)) ◇ y) = x := by
    intro x y
    have E8 : ∀ (v0 v1 : G), ((v0 ◇ (v0 ◇ v1)) ◇ v1) = v0 := by intro v0 v1; have ia := h v0 v1 v1; have ib := square_left_identity v1 (((v0 ◇ (v0 ◇ v1)) ◇ v1)); have step : ((v1 ◇ v1) ◇ ((v0 ◇ (v0 ◇ v1)) ◇ v1)) = ((v0 ◇ (v0 ◇ v1)) ◇ v1) := congrArg (fun __pc_hole => __pc_hole) (ib); exact step.symm.trans ((ia).symm)
    have target : ∀ (v0 v1 : G), ((v0 ◇ (v0 ◇ v1)) ◇ v1) = v0 := fun v0 v1 => E8 v0 v1
    exact target x y
  have square_absorption : ∀ x y : G, ((x ◇ (y ◇ y)) ◇ x) = x := by
    intro x y
    have E23 : ∀ (v0 v1 : G), ((v0 ◇ (v1 ◇ v1)) ◇ v0) = v0 := by intro v0 v1; have ia := t_cancellation v0 v0; have ib := squares_equal v0 v1; have step : ((v0 ◇ (v0 ◇ v0)) ◇ v0) = ((v0 ◇ (v1 ◇ v1)) ◇ v0) := congrArg (fun __pc_hole => ((v0 ◇ __pc_hole) ◇ v0)) (ib); exact step.symm.trans (ia)
    have target : ∀ (v0 v1 : G), ((v0 ◇ (v1 ◇ v1)) ◇ v0) = v0 := fun v0 v1 => E23 v0 v1
    exact target x y
  have square_transport : ∀ x y : G, (x ◇ (y ◇ y)) = (x ◇ x) := by
    intro x y
    have E32 : ∀ (v0 v1 : G), (((v0 ◇ (v1 ◇ v1)) ◇ v0) ◇ v0) = (v0 ◇ (v1 ◇ v1)) := by intro v0 v1; have ia := t_cancellation ((v0 ◇ (v1 ◇ v1))) v0; have ib := square_absorption v0 v1; have step : (((v0 ◇ (v1 ◇ v1)) ◇ ((v0 ◇ (v1 ◇ v1)) ◇ v0)) ◇ v0) = (((v0 ◇ (v1 ◇ v1)) ◇ v0) ◇ v0) := congrArg (fun __pc_hole => (((v0 ◇ (v1 ◇ v1)) ◇ __pc_hole) ◇ v0)) (ib); exact step.symm.trans (ia)
    have E247 : ∀ (v0 v1 : G), (v0 ◇ v0) = (v0 ◇ (v1 ◇ v1)) := by intro v0 v1; have ia := E32 v0 v1; have ib := square_absorption v0 v1; have step : (((v0 ◇ (v1 ◇ v1)) ◇ v0) ◇ v0) = (v0 ◇ v0) := congrArg (fun __pc_hole => (__pc_hole ◇ v0)) (ib); exact step.symm.trans (ia)
    have target : ∀ (v0 v1 : G), (v0 ◇ v0) = (v0 ◇ (v1 ◇ v1)) := fun v0 v1 => E247 v0 v1
    exact (target x y).symm
  have carrier_collapse : ∀ x y : G, x = y := by
    intro x y
    have E36 : ∀ (v0 v1 v2 : G), ((v0 ◇ (v1 ◇ v1)) ◇ ((v2 ◇ (v2 ◇ v0)) ◇ (v2 ◇ (v2 ◇ v0)))) = v2 := by intro v0 v1 v2; have ia := h v2 v0 ((v1 ◇ v1)); have ib := square_transport ((v2 ◇ (v2 ◇ v0))) v1; have step : ((v0 ◇ (v1 ◇ v1)) ◇ ((v2 ◇ (v2 ◇ v0)) ◇ (v1 ◇ v1))) = ((v0 ◇ (v1 ◇ v1)) ◇ ((v2 ◇ (v2 ◇ v0)) ◇ (v2 ◇ (v2 ◇ v0)))) := congrArg (fun __pc_hole => ((v0 ◇ (v1 ◇ v1)) ◇ __pc_hole)) (ib); exact step.symm.trans ((ia).symm)
    have E98 : ∀ (v0 v1 : G), ((v0 ◇ (v0 ◇ v0)) ◇ (v1 ◇ v1)) = v0 := by intro v0 v1; have ia := t_cancellation v0 ((v1 ◇ v1)); have ib := square_transport v0 v1; have step : ((v0 ◇ (v0 ◇ (v1 ◇ v1))) ◇ (v1 ◇ v1)) = ((v0 ◇ (v0 ◇ v0)) ◇ (v1 ◇ v1)) := congrArg (fun __pc_hole => ((v0 ◇ __pc_hole) ◇ (v1 ◇ v1))) (ib); exact step.symm.trans (ia)
    have E3031 : ∀ (v0 v1 : G), v0 = v1 := by intro v0 v1; have ia := E36 v0 v0 v1; have ib := E98 v0 ((v1 ◇ (v1 ◇ v0))); have step : ((v0 ◇ (v0 ◇ v0)) ◇ ((v1 ◇ (v1 ◇ v0)) ◇ (v1 ◇ (v1 ◇ v0)))) = v0 := congrArg (fun __pc_hole => __pc_hole) (ib); exact step.symm.trans (ia)
    have target : ∀ (v0 v1 : G), v0 = v1 := fun v0 v1 => E3031 v0 v1
    exact target x y
  intro x y z w
  exact carrier_collapse _ _
