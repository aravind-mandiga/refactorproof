-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isDigit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def countDigits_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def countDigits (s : String) (h_precond : countDigits_precond (s)) : Nat :=
  List.length (List.filter isDigit s.toList)
end RPOrig

namespace RPRef
private def countDigits__rp_helper_df69abf7 (s : String) (h_precond : countDigits_precond (s)) : Nat :=
  List.length (List.filter isDigit s.toList)

def countDigits (s : String) (h_precond : countDigits_precond (s)) : Nat :=
  countDigits__rp_helper_df69abf7 s h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : countDigits_precond (s)) :
    RPOrig.countDigits s h_precond = RPRef.countDigits s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : countDigits_precond (s)) :
    RPOrig.countDigits s h_precond = RPRef.countDigits s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : countDigits_precond (s)) :
    RPOrig.countDigits s h_precond = RPRef.countDigits s h_precond := by
  delta RPOrig.countDigits RPRef.countDigits RPRef.countDigits__rp_helper_df69abf7
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : countDigits_precond (s)) :
    RPOrig.countDigits s h_precond = RPRef.countDigits s h_precond := by
  (simp only [RPOrig.countDigits, RPRef.countDigits, RPRef.countDigits__rp_helper_df69abf7]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.countDigits RPRef.countDigits RPRef.countDigits__rp_helper_df69abf7; rfl))

theorem rp_equiv_simp (s : String) (h_precond : countDigits_precond (s)) :
    RPOrig.countDigits s h_precond = RPRef.countDigits s h_precond := by
  (simp [RPOrig.countDigits, RPRef.countDigits, RPRef.countDigits__rp_helper_df69abf7]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.countDigits RPRef.countDigits RPRef.countDigits__rp_helper_df69abf7; rfl))
