-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def containsConsecutiveNumbers_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def containsConsecutiveNumbers (a : Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) : Bool :=
  if a.size ≤ 1 then
    false
  else
    let withIndices := a.mapIdx (fun i x => (i, x))
    withIndices.any (fun (i, x) =>
      i < a.size - 1 && x + 1 == a[i+1]!)
end RPOrig

namespace RPRef

noncomputable def containsConsecutiveNumbers (a : Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) : Bool :=
  let __rp_tmp_24bebd1c : Bool :=
    if a.size ≤ 1 then
      false
    else
      let withIndices := a.mapIdx (fun i x => (i, x))
      withIndices.any (fun (i, x) =>
        i < a.size - 1 && x + 1 == a[i+1]!)
  __rp_tmp_24bebd1c
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) :
    RPOrig.containsConsecutiveNumbers a h_precond = RPRef.containsConsecutiveNumbers a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) :
    RPOrig.containsConsecutiveNumbers a h_precond = RPRef.containsConsecutiveNumbers a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) :
    RPOrig.containsConsecutiveNumbers a h_precond = RPRef.containsConsecutiveNumbers a h_precond := by
  delta RPOrig.containsConsecutiveNumbers RPRef.containsConsecutiveNumbers
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) :
    RPOrig.containsConsecutiveNumbers a h_precond = RPRef.containsConsecutiveNumbers a h_precond := by
  (simp only [RPOrig.containsConsecutiveNumbers, RPRef.containsConsecutiveNumbers]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.containsConsecutiveNumbers RPRef.containsConsecutiveNumbers; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : containsConsecutiveNumbers_precond (a)) :
    RPOrig.containsConsecutiveNumbers a h_precond = RPRef.containsConsecutiveNumbers a h_precond := by
  (simp [RPOrig.containsConsecutiveNumbers, RPRef.containsConsecutiveNumbers]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.containsConsecutiveNumbers RPRef.containsConsecutiveNumbers; rfl))
