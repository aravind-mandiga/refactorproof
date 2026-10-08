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

def reverse (a : Array Int) (h_precond : reverse_precond (a)) : Array Int :=
  let __rp_tmp_30a967f6 : Array Int :=
    reverse_core a 0
  __rp_tmp_30a967f6
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : reverse_precond (a)) :
    RPOrig.reverse a h_precond = RPRef.reverse a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : reverse_precond (a)) :
    RPOrig.reverse a h_precond = RPRef.reverse a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : reverse_precond (a)) :
    RPOrig.reverse a h_precond = RPRef.reverse a h_precond := by
  delta RPOrig.reverse RPRef.reverse
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : reverse_precond (a)) :
    RPOrig.reverse a h_precond = RPRef.reverse a h_precond := by
  (simp only [RPOrig.reverse, RPRef.reverse]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.reverse RPRef.reverse; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : reverse_precond (a)) :
    RPOrig.reverse a h_precond = RPRef.reverse a h_precond := by
  (simp [RPOrig.reverse, RPRef.reverse]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.reverse RPRef.reverse; rfl))
