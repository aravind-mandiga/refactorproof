-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def ToArray_precond (xs : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def ToArray (xs : List Int) (h_precond : ToArray_precond (xs)) : Array Int :=
  xs.toArray
end RPOrig

namespace RPRef
private def ToArray__rp_helper_a2d904a6 (xs : List Int) (h_precond : ToArray_precond (xs)) : Array Int :=
  xs.toArray

def ToArray (xs : List Int) (h_precond : ToArray_precond (xs)) : Array Int :=
  ToArray__rp_helper_a2d904a6 xs h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (xs : List Int) (h_precond : ToArray_precond (xs)) :
    RPOrig.ToArray xs h_precond = RPRef.ToArray xs h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (xs : List Int) (h_precond : ToArray_precond (xs)) :
    RPOrig.ToArray xs h_precond = RPRef.ToArray xs h_precond := rfl

theorem rp_equiv_delta_rfl (xs : List Int) (h_precond : ToArray_precond (xs)) :
    RPOrig.ToArray xs h_precond = RPRef.ToArray xs h_precond := by
  delta RPOrig.ToArray RPRef.ToArray RPRef.ToArray__rp_helper_a2d904a6
  rfl

theorem rp_equiv_simp_only (xs : List Int) (h_precond : ToArray_precond (xs)) :
    RPOrig.ToArray xs h_precond = RPRef.ToArray xs h_precond := by
  (simp only [RPOrig.ToArray, RPRef.ToArray, RPRef.ToArray__rp_helper_a2d904a6]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ToArray RPRef.ToArray RPRef.ToArray__rp_helper_a2d904a6; rfl))

theorem rp_equiv_simp (xs : List Int) (h_precond : ToArray_precond (xs)) :
    RPOrig.ToArray xs h_precond = RPRef.ToArray xs h_precond := by
  (simp [RPOrig.ToArray, RPRef.ToArray, RPRef.ToArray__rp_helper_a2d904a6]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ToArray RPRef.ToArray RPRef.ToArray__rp_helper_a2d904a6; rfl))
