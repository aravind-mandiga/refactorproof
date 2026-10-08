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
private def singleDigitPrimeFactor__rp_branch_4e87d626 (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) : Nat :=
  if n % 2 == 0 then 2
   else if n % 3 == 0 then 3
   else if n % 5 == 0 then 5
   else if n % 7 == 0 then 7
   else 0

def singleDigitPrimeFactor (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) : Nat :=
  if n == 0 then 0
  else
    singleDigitPrimeFactor__rp_branch_4e87d626 n h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    RPOrig.singleDigitPrimeFactor n h_precond = RPRef.singleDigitPrimeFactor n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    RPOrig.singleDigitPrimeFactor n h_precond = RPRef.singleDigitPrimeFactor n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    RPOrig.singleDigitPrimeFactor n h_precond = RPRef.singleDigitPrimeFactor n h_precond := by
  first
    | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor__rp_branch_4e87d626; rfl)
    | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor__rp_branch_4e87d626 RPOrig.singleDigitPrimeFactor._unary; rfl)
    | (set_option smartUnfolding false in rfl)

theorem rp_equiv_simp_only (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    RPOrig.singleDigitPrimeFactor n h_precond = RPRef.singleDigitPrimeFactor n h_precond := by
  (simp only [RPOrig.singleDigitPrimeFactor, RPRef.singleDigitPrimeFactor, RPRef.singleDigitPrimeFactor__rp_branch_4e87d626]) <;> (first | rfl | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor__rp_branch_4e87d626; rfl) | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor__rp_branch_4e87d626 RPOrig.singleDigitPrimeFactor._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : singleDigitPrimeFactor_precond (n)) :
    RPOrig.singleDigitPrimeFactor n h_precond = RPRef.singleDigitPrimeFactor n h_precond := by
  (simp [RPOrig.singleDigitPrimeFactor, RPRef.singleDigitPrimeFactor, RPRef.singleDigitPrimeFactor__rp_branch_4e87d626]) <;> (first | rfl | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor__rp_branch_4e87d626; rfl) | (delta RPOrig.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor RPRef.singleDigitPrimeFactor__rp_branch_4e87d626 RPOrig.singleDigitPrimeFactor._unary; rfl) | (set_option smartUnfolding false in rfl))
