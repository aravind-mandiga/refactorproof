-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def singleDigitPrimeFactor_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def singleDigitPrimeFactor (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) : Nat :=
  if n == 0 then 0
  else if n % 2 == 0 then 2
  else if n % 3 == 0 then 3
  else if n % 5 == 0 then 5
  else if n % 7 == 0 then 7
  else 0
end RPOrig

namespace RPRef

def singleDigitPrimeFactor (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) : Nat :=
  if ¬ (n == 0) then if n % 2 == 0 then 2
  else if n % 3 == 0 then 3
  else if n % 5 == 0 then 5
  else if n % 7 == 0 then 7
  else 0
  else 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    RPOrig.singleDigitPrimeFactor n h_precond = RPRef.singleDigitPrimeFactor n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    RPOrig.singleDigitPrimeFactor n h_precond = RPRef.singleDigitPrimeFactor n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    RPOrig.singleDigitPrimeFactor n h_precond = RPRef.singleDigitPrimeFactor n h_precond := by
  delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor
  rfl

theorem rp_equiv_simp_only (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    RPOrig.singleDigitPrimeFactor n h_precond = RPRef.singleDigitPrimeFactor n h_precond := by
  first
    | (simp only [RPOrig.singleDigitPrimeFactor, RPRef.singleDigitPrimeFactor, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor; rfl))
    | (simp only [RPOrig.singleDigitPrimeFactor, RPRef.singleDigitPrimeFactor, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor; rfl))
    | (simp only [RPOrig.singleDigitPrimeFactor, RPRef.singleDigitPrimeFactor]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor; rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    RPOrig.singleDigitPrimeFactor n h_precond = RPRef.singleDigitPrimeFactor n h_precond := by
  first
    | (simp [RPOrig.singleDigitPrimeFactor, RPRef.singleDigitPrimeFactor, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor; rfl))
    | (simp [RPOrig.singleDigitPrimeFactor, RPRef.singleDigitPrimeFactor, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor; rfl))
    | (simp [RPOrig.singleDigitPrimeFactor, RPRef.singleDigitPrimeFactor]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor; rfl))

theorem rp_equiv_bycases (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    RPOrig.singleDigitPrimeFactor n h_precond = RPRef.singleDigitPrimeFactor n h_precond := by
  by_cases h : (n == 0) <;> (try simp [h, RPOrig.singleDigitPrimeFactor, RPRef.singleDigitPrimeFactor]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor; rfl))

theorem rp_equiv_bycases_ite (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    RPOrig.singleDigitPrimeFactor n h_precond = RPRef.singleDigitPrimeFactor n h_precond := by
  by_cases h : (n == 0) <;> (try simp [h, ite_not, RPOrig.singleDigitPrimeFactor, RPRef.singleDigitPrimeFactor]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor; rfl))

theorem rp_equiv_split_simp_all (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    RPOrig.singleDigitPrimeFactor n h_precond = RPRef.singleDigitPrimeFactor n h_precond := by
  simp only [RPOrig.singleDigitPrimeFactor, RPRef.singleDigitPrimeFactor]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor; rfl))
