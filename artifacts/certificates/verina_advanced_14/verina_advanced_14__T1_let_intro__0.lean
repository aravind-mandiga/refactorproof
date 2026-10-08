-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def ifPowerOfFour_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def ifPowerOfFour (n : Nat) (h_precond : ifPowerOfFour_precond (n)) : Bool :=
  let rec helper (n : Nat) : Bool :=
    match n with
    | 0 =>
      false
    | Nat.succ m =>
      match m with
      | 0 =>
        true
      | Nat.succ l =>
        if (l+2)%4=0 then
          helper ((l+2)/4)
        else
          false
  helper n
end RPOrig

namespace RPRef

def ifPowerOfFour (n : Nat) (h_precond : ifPowerOfFour_precond (n)) : Bool :=
  let __rp_tmp_ebf1b3a7 : Bool :=
    let rec helper (n : Nat) : Bool :=
      match n with
      | 0 =>
        false
      | Nat.succ m =>
        match m with
        | 0 =>
          true
        | Nat.succ l =>
          if (l+2)%4=0 then
            helper ((l+2)/4)
          else
            false
    helper n
  __rp_tmp_ebf1b3a7
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (h_precond : ifPowerOfFour_precond (n)) :
    RPOrig.ifPowerOfFour n h_precond = RPRef.ifPowerOfFour n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (h_precond : ifPowerOfFour_precond (n)) :
    RPOrig.ifPowerOfFour n h_precond = RPRef.ifPowerOfFour n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (h_precond : ifPowerOfFour_precond (n)) :
    RPOrig.ifPowerOfFour n h_precond = RPRef.ifPowerOfFour n h_precond := by
  delta RPOrig.ifPowerOfFour RPRef.ifPowerOfFour RPOrig.ifPowerOfFour.helper RPRef.ifPowerOfFour.helper
  rfl

theorem rp_equiv_simp_only (n : Nat) (h_precond : ifPowerOfFour_precond (n)) :
    RPOrig.ifPowerOfFour n h_precond = RPRef.ifPowerOfFour n h_precond := by
  (simp only [RPOrig.ifPowerOfFour, RPRef.ifPowerOfFour]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ifPowerOfFour RPRef.ifPowerOfFour RPOrig.ifPowerOfFour.helper RPRef.ifPowerOfFour.helper; rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : ifPowerOfFour_precond (n)) :
    RPOrig.ifPowerOfFour n h_precond = RPRef.ifPowerOfFour n h_precond := by
  (simp [RPOrig.ifPowerOfFour, RPRef.ifPowerOfFour]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ifPowerOfFour RPRef.ifPowerOfFour RPOrig.ifPowerOfFour.helper RPRef.ifPowerOfFour.helper; rfl))
