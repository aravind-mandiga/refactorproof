-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def reverse_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def reverse_core (arr : Array Int) (i : Nat) : Array Int :=
  if i < arr.size / 2 then
    let j := arr.size - 1 - i
    let temp := arr[i]!
    let arr' := arr.set! i (arr[j]!)
    let arr'' := arr'.set! j temp
    reverse_core arr'' (i + 1)
  else
    arr

namespace RPOrig

def reverse (a : Array Int) (h_precond : reverse_precond (a)) : Array Int :=
  reverse_core a 0
end RPOrig

namespace RPRef

private def reverse__rp_helper_3dce61b4 (a : Array Int) (h_precond : reverse_precond (a)) : Array Int :=
  reverse_core a 0

def reverse (a : Array Int) (h_precond : reverse_precond (a)) : Array Int :=
  reverse__rp_helper_3dce61b4 a h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : reverse_precond (a)) :
    RPOrig.reverse a h_precond = RPRef.reverse a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : reverse_precond (a)) :
    RPOrig.reverse a h_precond = RPRef.reverse a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : reverse_precond (a)) :
    RPOrig.reverse a h_precond = RPRef.reverse a h_precond := by
  delta RPOrig.reverse RPRef.reverse RPRef.reverse__rp_helper_3dce61b4
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : reverse_precond (a)) :
    RPOrig.reverse a h_precond = RPRef.reverse a h_precond := by
  (simp only [RPOrig.reverse, RPRef.reverse, RPRef.reverse__rp_helper_3dce61b4]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.reverse RPRef.reverse RPRef.reverse__rp_helper_3dce61b4; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : reverse_precond (a)) :
    RPOrig.reverse a h_precond = RPRef.reverse a h_precond := by
  (simp [RPOrig.reverse, RPRef.reverse, RPRef.reverse__rp_helper_3dce61b4]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.reverse RPRef.reverse RPRef.reverse__rp_helper_3dce61b4; rfl))
