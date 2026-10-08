-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def lastDigit_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def lastDigit (n : Nat) (h_precond : lastDigit_precond (n)) : Nat :=
  n % 10
end RPOrig

namespace RPRef

def lastDigit (n : Nat) (h_precond : lastDigit_precond (n)) : Nat :=
  let __rp_tmp_c1b8a8ca : Nat :=
    n % 10
  __rp_tmp_c1b8a8ca
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (h_precond : lastDigit_precond (n)) :
    RPOrig.lastDigit n h_precond = RPRef.lastDigit n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (h_precond : lastDigit_precond (n)) :
    RPOrig.lastDigit n h_precond = RPRef.lastDigit n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (h_precond : lastDigit_precond (n)) :
    RPOrig.lastDigit n h_precond = RPRef.lastDigit n h_precond := by
  delta RPOrig.lastDigit RPRef.lastDigit
  rfl

theorem rp_equiv_simp_only (n : Nat) (h_precond : lastDigit_precond (n)) :
    RPOrig.lastDigit n h_precond = RPRef.lastDigit n h_precond := by
  (simp only [RPOrig.lastDigit, RPRef.lastDigit]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lastDigit RPRef.lastDigit; rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : lastDigit_precond (n)) :
    RPOrig.lastDigit n h_precond = RPRef.lastDigit n h_precond := by
  (simp [RPOrig.lastDigit, RPRef.lastDigit]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lastDigit RPRef.lastDigit; rfl))
