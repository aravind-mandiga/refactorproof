-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def double_array_elements_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def double_array_elements_aux (s_old s : Array Int) (i : Nat) : Array Int :=
  if i < s.size then
    let new_s := s.set! i (2 * (s_old[i]!))
    double_array_elements_aux s_old new_s (i + 1)
  else
    s

namespace RPOrig

def double_array_elements (s : Array Int) (h_precond : double_array_elements_precond (s)) : Array Int :=
  double_array_elements_aux s s 0
end RPOrig

namespace RPRef

private def double_array_elements__rp_helper_8a291435 (s : Array Int) (h_precond : double_array_elements_precond (s)) : Array Int :=
  double_array_elements_aux s s 0

def double_array_elements (s : Array Int) (h_precond : double_array_elements_precond (s)) : Array Int :=
  double_array_elements__rp_helper_8a291435 s h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : Array Int) (h_precond : double_array_elements_precond (s)) :
    RPOrig.double_array_elements s h_precond = RPRef.double_array_elements s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : Array Int) (h_precond : double_array_elements_precond (s)) :
    RPOrig.double_array_elements s h_precond = RPRef.double_array_elements s h_precond := rfl

theorem rp_equiv_delta_rfl (s : Array Int) (h_precond : double_array_elements_precond (s)) :
    RPOrig.double_array_elements s h_precond = RPRef.double_array_elements s h_precond := by
  delta RPOrig.double_array_elements RPRef.double_array_elements RPRef.double_array_elements__rp_helper_8a291435
  rfl

theorem rp_equiv_simp_only (s : Array Int) (h_precond : double_array_elements_precond (s)) :
    RPOrig.double_array_elements s h_precond = RPRef.double_array_elements s h_precond := by
  (simp only [RPOrig.double_array_elements, RPRef.double_array_elements, RPRef.double_array_elements__rp_helper_8a291435]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.double_array_elements RPRef.double_array_elements RPRef.double_array_elements__rp_helper_8a291435; rfl))

theorem rp_equiv_simp (s : Array Int) (h_precond : double_array_elements_precond (s)) :
    RPOrig.double_array_elements s h_precond = RPRef.double_array_elements s h_precond := by
  (simp [RPOrig.double_array_elements, RPRef.double_array_elements, RPRef.double_array_elements__rp_helper_8a291435]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.double_array_elements RPRef.double_array_elements RPRef.double_array_elements__rp_helper_8a291435; rfl))
