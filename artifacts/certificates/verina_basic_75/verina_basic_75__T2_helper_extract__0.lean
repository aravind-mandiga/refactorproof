-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def minArray_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def loop (a : Array Int) (i : Nat) (currentMin : Int) : Int :=
  if i < a.size then
    let newMin := if currentMin > a[i]! then a[i]! else currentMin
    loop a (i + 1) newMin
  else
    currentMin

namespace RPOrig

def minArray (a : Array Int) (h_precond : minArray_precond (a)) : Int :=
  loop a 1 (a[0]!)
end RPOrig

namespace RPRef

private def minArray__rp_helper_c465a41f (a : Array Int) (h_precond : minArray_precond (a)) : Int :=
  loop a 1 (a[0]!)

def minArray (a : Array Int) (h_precond : minArray_precond (a)) : Int :=
  minArray__rp_helper_c465a41f a h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : minArray_precond (a)) :
    RPOrig.minArray a h_precond = RPRef.minArray a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : minArray_precond (a)) :
    RPOrig.minArray a h_precond = RPRef.minArray a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : minArray_precond (a)) :
    RPOrig.minArray a h_precond = RPRef.minArray a h_precond := by
  delta RPOrig.minArray RPRef.minArray RPRef.minArray__rp_helper_c465a41f
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : minArray_precond (a)) :
    RPOrig.minArray a h_precond = RPRef.minArray a h_precond := by
  (simp only [RPOrig.minArray, RPRef.minArray, RPRef.minArray__rp_helper_c465a41f]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minArray RPRef.minArray RPRef.minArray__rp_helper_c465a41f; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : minArray_precond (a)) :
    RPOrig.minArray a h_precond = RPRef.minArray a h_precond := by
  (simp [RPOrig.minArray, RPRef.minArray, RPRef.minArray__rp_helper_c465a41f]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minArray RPRef.minArray RPRef.minArray__rp_helper_c465a41f; rfl))
