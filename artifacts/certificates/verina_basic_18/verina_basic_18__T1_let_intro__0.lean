-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sumOfDigits_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def sumOfDigits (n : Nat) (h_precond : sumOfDigits_precond (n)) : Nat :=
  let rec loop (n : Nat) (acc : Nat) : Nat :=
    if n = 0 then acc
    else loop (n / 10) (acc + n % 10)
  loop n 0
end RPOrig

namespace RPRef

def sumOfDigits (n : Nat) (h_precond : sumOfDigits_precond (n)) : Nat :=
  let __rp_tmp_819ad26d : Nat :=
    let rec loop (n : Nat) (acc : Nat) : Nat :=
      if n = 0 then acc
      else loop (n / 10) (acc + n % 10)
    loop n 0
  __rp_tmp_819ad26d
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (h_precond : sumOfDigits_precond (n)) :
    RPOrig.sumOfDigits n h_precond = RPRef.sumOfDigits n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (h_precond : sumOfDigits_precond (n)) :
    RPOrig.sumOfDigits n h_precond = RPRef.sumOfDigits n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (h_precond : sumOfDigits_precond (n)) :
    RPOrig.sumOfDigits n h_precond = RPRef.sumOfDigits n h_precond := by
  delta RPOrig.sumOfDigits RPRef.sumOfDigits RPOrig.sumOfDigits.loop RPRef.sumOfDigits.loop
  rfl

theorem rp_equiv_simp_only (n : Nat) (h_precond : sumOfDigits_precond (n)) :
    RPOrig.sumOfDigits n h_precond = RPRef.sumOfDigits n h_precond := by
  (simp only [RPOrig.sumOfDigits, RPRef.sumOfDigits]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfDigits RPRef.sumOfDigits RPOrig.sumOfDigits.loop RPRef.sumOfDigits.loop; rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : sumOfDigits_precond (n)) :
    RPOrig.sumOfDigits n h_precond = RPRef.sumOfDigits n h_precond := by
  (simp [RPOrig.sumOfDigits, RPRef.sumOfDigits]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.sumOfDigits RPRef.sumOfDigits RPOrig.sumOfDigits.loop RPRef.sumOfDigits.loop; rfl))
