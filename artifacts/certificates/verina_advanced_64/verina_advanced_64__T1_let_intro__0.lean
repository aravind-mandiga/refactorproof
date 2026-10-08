-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def removeElement_precond (lst : List Nat) (target : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def removeElement (lst : List Nat) (target : Nat) (h_precond : removeElement_precond (lst) (target)) : List Nat :=
  let rec helper (lst : List Nat) (target : Nat) : List Nat :=
    match lst with
    | [] => []
    | x :: xs =>
      let rest := helper xs target
      if x = target then rest else x :: rest
  helper lst target
end RPOrig

namespace RPRef

def removeElement (lst : List Nat) (target : Nat) (h_precond : removeElement_precond (lst) (target)) : List Nat :=
  let __rp_tmp_b50f7237 : List Nat :=
    let rec helper (lst : List Nat) (target : Nat) : List Nat :=
      match lst with
      | [] => []
      | x :: xs =>
        let rest := helper xs target
        if x = target then rest else x :: rest
    helper lst target
  __rp_tmp_b50f7237
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (lst : List Nat) (target : Nat) (h_precond : removeElement_precond (lst) (target)) :
    RPOrig.removeElement lst target h_precond = RPRef.removeElement lst target h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (lst : List Nat) (target : Nat) (h_precond : removeElement_precond (lst) (target)) :
    RPOrig.removeElement lst target h_precond = RPRef.removeElement lst target h_precond := rfl

theorem rp_equiv_delta_rfl (lst : List Nat) (target : Nat) (h_precond : removeElement_precond (lst) (target)) :
    RPOrig.removeElement lst target h_precond = RPRef.removeElement lst target h_precond := by
  delta RPOrig.removeElement RPRef.removeElement RPOrig.removeElement.helper RPRef.removeElement.helper
  rfl

theorem rp_equiv_simp_only (lst : List Nat) (target : Nat) (h_precond : removeElement_precond (lst) (target)) :
    RPOrig.removeElement lst target h_precond = RPRef.removeElement lst target h_precond := by
  (simp only [RPOrig.removeElement, RPRef.removeElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeElement RPRef.removeElement RPOrig.removeElement.helper RPRef.removeElement.helper; rfl))

theorem rp_equiv_simp (lst : List Nat) (target : Nat) (h_precond : removeElement_precond (lst) (target)) :
    RPOrig.removeElement lst target h_precond = RPRef.removeElement lst target h_precond := by
  (simp [RPOrig.removeElement, RPRef.removeElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeElement RPRef.removeElement RPOrig.removeElement.helper RPRef.removeElement.helper; rfl))
