-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def isItEight_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def isItEight (n : Int) (h_precond : isItEight_precond (n)) : Bool :=
  let rec hasDigitEight (m : Nat) : Bool :=
    if m <= 0 then false
    else if m % 10 == 8 then true
    else hasDigitEight (m / 10)
    termination_by m

  let absN := Int.natAbs n
  n % 8 == 0 || hasDigitEight absN
end RPOrig

namespace RPRef

def isItEight (n : Int) (h_precond : isItEight_precond (n)) : Bool :=
  let __rp_tmp_eba621c4 : Bool :=
    let rec hasDigitEight (m : Nat) : Bool :=
      if m <= 0 then false
      else if m % 10 == 8 then true
      else hasDigitEight (m / 10)
      termination_by m

    let absN := Int.natAbs n
    n % 8 == 0 || hasDigitEight absN
  __rp_tmp_eba621c4
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Int) (h_precond : isItEight_precond (n)) :
    RPOrig.isItEight n h_precond = RPRef.isItEight n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Int) (h_precond : isItEight_precond (n)) :
    RPOrig.isItEight n h_precond = RPRef.isItEight n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Int) (h_precond : isItEight_precond (n)) :
    RPOrig.isItEight n h_precond = RPRef.isItEight n h_precond := by
  delta RPOrig.isItEight RPRef.isItEight RPOrig.isItEight.hasDigitEight RPRef.isItEight.hasDigitEight
  rfl

theorem rp_equiv_simp_only (n : Int) (h_precond : isItEight_precond (n)) :
    RPOrig.isItEight n h_precond = RPRef.isItEight n h_precond := by
  (simp only [RPOrig.isItEight, RPRef.isItEight]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isItEight RPRef.isItEight RPOrig.isItEight.hasDigitEight RPRef.isItEight.hasDigitEight; rfl))

theorem rp_equiv_simp (n : Int) (h_precond : isItEight_precond (n)) :
    RPOrig.isItEight n h_precond = RPRef.isItEight n h_precond := by
  (simp [RPOrig.isItEight, RPRef.isItEight]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isItEight RPRef.isItEight RPOrig.isItEight.hasDigitEight RPRef.isItEight.hasDigitEight; rfl))
