-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def maxArray_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def maxArray_aux (a : Array Int) (index : Nat) (current : Int) : Int :=
  if index < a.size then
    let new_current := if current > a[index]! then current else a[index]!
    maxArray_aux a (index + 1) new_current
  else
    current

namespace RPOrig

def maxArray (a : Array Int) (h_precond : maxArray_precond (a)) : Int :=
  maxArray_aux a 1 a[0]!
end RPOrig

namespace RPRef

def maxArray (a : Array Int) (h_precond : maxArray_precond (a)) : Int :=
  let __rp_tmp_3108e807 : Int :=
    maxArray_aux a 1 a[0]!
  __rp_tmp_3108e807
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : maxArray_precond (a)) :
    RPOrig.maxArray a h_precond = RPRef.maxArray a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : maxArray_precond (a)) :
    RPOrig.maxArray a h_precond = RPRef.maxArray a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : maxArray_precond (a)) :
    RPOrig.maxArray a h_precond = RPRef.maxArray a h_precond := by
  delta RPOrig.maxArray RPRef.maxArray
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : maxArray_precond (a)) :
    RPOrig.maxArray a h_precond = RPRef.maxArray a h_precond := by
  (simp only [RPOrig.maxArray, RPRef.maxArray]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxArray RPRef.maxArray; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : maxArray_precond (a)) :
    RPOrig.maxArray a h_precond = RPRef.maxArray a h_precond := by
  (simp [RPOrig.maxArray, RPRef.maxArray]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxArray RPRef.maxArray; rfl))
