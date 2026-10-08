-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isSorted_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def isSorted (a : Array Int) (h_precond : isSorted_precond (a)) : Bool :=
  if a.size ≤ 1 then
    true
  else
    a.mapIdx (fun i x =>
      if h : i + 1 < a.size then
        decide (x ≤ a[i + 1])
      else
        true) |>.all id
end RPOrig

namespace RPRef
private def isSorted__rp_helper_f8cad7cc (a : Array Int) (h_precond : isSorted_precond (a)) : Bool :=
  if a.size ≤ 1 then
    true
  else
    a.mapIdx (fun i x =>
      if h : i + 1 < a.size then
        decide (x ≤ a[i + 1])
      else
        true) |>.all id

def isSorted (a : Array Int) (h_precond : isSorted_precond (a)) : Bool :=
  isSorted__rp_helper_f8cad7cc a h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : isSorted_precond (a)) :
    RPOrig.isSorted a h_precond = RPRef.isSorted a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : isSorted_precond (a)) :
    RPOrig.isSorted a h_precond = RPRef.isSorted a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : isSorted_precond (a)) :
    RPOrig.isSorted a h_precond = RPRef.isSorted a h_precond := by
  delta RPOrig.isSorted RPRef.isSorted RPRef.isSorted__rp_helper_f8cad7cc
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : isSorted_precond (a)) :
    RPOrig.isSorted a h_precond = RPRef.isSorted a h_precond := by
  (simp only [RPOrig.isSorted, RPRef.isSorted, RPRef.isSorted__rp_helper_f8cad7cc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSorted RPRef.isSorted RPRef.isSorted__rp_helper_f8cad7cc; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : isSorted_precond (a)) :
    RPOrig.isSorted a h_precond = RPRef.isSorted a h_precond := by
  (simp [RPOrig.isSorted, RPRef.isSorted, RPRef.isSorted__rp_helper_f8cad7cc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSorted RPRef.isSorted RPRef.isSorted__rp_helper_f8cad7cc; rfl))
