-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def maxOfList_precond (lst : List Nat) : Prop :=
  -- !benchmark @start precond
  lst.length > 0
  -- !benchmark @end precond



namespace RPOrig

def maxOfList (lst : List Nat) (h_precond : maxOfList_precond (lst)) : Nat :=
  let rec helper (lst : List Nat) : Nat :=
    match lst with
    | [] => 0  -- technically shouldn't happen if input is always non-empty
    | [x] => x
    | x :: xs =>
      let maxTail := helper xs
      if x > maxTail then x else maxTail

  helper lst
end RPOrig

namespace RPRef
private def maxOfList__rp_helper_96f14f72 (lst : List Nat) (h_precond : maxOfList_precond (lst)) : Nat :=
  let rec helper (lst : List Nat) : Nat :=
    match lst with
    | [] => 0  -- technically shouldn't happen if input is always non-empty
    | [x] => x
    | x :: xs =>
      let maxTail := helper xs
      if x > maxTail then x else maxTail

  helper lst

def maxOfList (lst : List Nat) (h_precond : maxOfList_precond (lst)) : Nat :=
  maxOfList__rp_helper_96f14f72 lst h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (lst : List Nat) (h_precond : maxOfList_precond (lst)) :
    RPOrig.maxOfList lst h_precond = RPRef.maxOfList lst h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (lst : List Nat) (h_precond : maxOfList_precond (lst)) :
    RPOrig.maxOfList lst h_precond = RPRef.maxOfList lst h_precond := rfl

theorem rp_equiv_delta_rfl (lst : List Nat) (h_precond : maxOfList_precond (lst)) :
    RPOrig.maxOfList lst h_precond = RPRef.maxOfList lst h_precond := by
  delta RPOrig.maxOfList RPRef.maxOfList RPRef.maxOfList__rp_helper_96f14f72 RPOrig.maxOfList.helper RPRef.maxOfList__rp_helper_96f14f72.helper
  rfl

theorem rp_equiv_simp_only (lst : List Nat) (h_precond : maxOfList_precond (lst)) :
    RPOrig.maxOfList lst h_precond = RPRef.maxOfList lst h_precond := by
  (simp only [RPOrig.maxOfList, RPRef.maxOfList, RPRef.maxOfList__rp_helper_96f14f72]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxOfList RPRef.maxOfList RPRef.maxOfList__rp_helper_96f14f72 RPOrig.maxOfList.helper RPRef.maxOfList__rp_helper_96f14f72.helper; rfl))

theorem rp_equiv_simp (lst : List Nat) (h_precond : maxOfList_precond (lst)) :
    RPOrig.maxOfList lst h_precond = RPRef.maxOfList lst h_precond := by
  (simp [RPOrig.maxOfList, RPRef.maxOfList, RPRef.maxOfList__rp_helper_96f14f72]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxOfList RPRef.maxOfList RPRef.maxOfList__rp_helper_96f14f72 RPOrig.maxOfList.helper RPRef.maxOfList__rp_helper_96f14f72.helper; rfl))
