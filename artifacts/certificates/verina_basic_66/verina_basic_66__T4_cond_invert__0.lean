-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def ComputeIsEven_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def ComputeIsEven (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
  if x % 2 = 0 then true else false
end RPOrig

namespace RPRef

def ComputeIsEven (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
  if ¬ (x % 2 = 0) then false
  else true
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (x : Int) (h_precond : ComputeIsEven_precond (x)) :
    RPOrig.ComputeIsEven x h_precond = RPRef.ComputeIsEven x h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (x : Int) (h_precond : ComputeIsEven_precond (x)) :
    RPOrig.ComputeIsEven x h_precond = RPRef.ComputeIsEven x h_precond := rfl

theorem rp_equiv_delta_rfl (x : Int) (h_precond : ComputeIsEven_precond (x)) :
    RPOrig.ComputeIsEven x h_precond = RPRef.ComputeIsEven x h_precond := by
  delta RPOrig.ComputeIsEven RPRef.ComputeIsEven
  rfl

theorem rp_equiv_simp_only (x : Int) (h_precond : ComputeIsEven_precond (x)) :
    RPOrig.ComputeIsEven x h_precond = RPRef.ComputeIsEven x h_precond := by
  first
    | (simp only [RPOrig.ComputeIsEven, RPRef.ComputeIsEven, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeIsEven RPRef.ComputeIsEven; rfl))
    | (simp only [RPOrig.ComputeIsEven, RPRef.ComputeIsEven, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeIsEven RPRef.ComputeIsEven; rfl))
    | (simp only [RPOrig.ComputeIsEven, RPRef.ComputeIsEven]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeIsEven RPRef.ComputeIsEven; rfl))

theorem rp_equiv_simp (x : Int) (h_precond : ComputeIsEven_precond (x)) :
    RPOrig.ComputeIsEven x h_precond = RPRef.ComputeIsEven x h_precond := by
  first
    | (simp [RPOrig.ComputeIsEven, RPRef.ComputeIsEven, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeIsEven RPRef.ComputeIsEven; rfl))
    | (simp [RPOrig.ComputeIsEven, RPRef.ComputeIsEven, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeIsEven RPRef.ComputeIsEven; rfl))
    | (simp [RPOrig.ComputeIsEven, RPRef.ComputeIsEven]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeIsEven RPRef.ComputeIsEven; rfl))

theorem rp_equiv_bycases (x : Int) (h_precond : ComputeIsEven_precond (x)) :
    RPOrig.ComputeIsEven x h_precond = RPRef.ComputeIsEven x h_precond := by
  by_cases h : (x % 2 = 0) <;> (try simp [h, RPOrig.ComputeIsEven, RPRef.ComputeIsEven]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeIsEven RPRef.ComputeIsEven; rfl))

theorem rp_equiv_bycases_ite (x : Int) (h_precond : ComputeIsEven_precond (x)) :
    RPOrig.ComputeIsEven x h_precond = RPRef.ComputeIsEven x h_precond := by
  by_cases h : (x % 2 = 0) <;> (try simp [h, ite_not, RPOrig.ComputeIsEven, RPRef.ComputeIsEven]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeIsEven RPRef.ComputeIsEven; rfl))

theorem rp_equiv_split_simp_all (x : Int) (h_precond : ComputeIsEven_precond (x)) :
    RPOrig.ComputeIsEven x h_precond = RPRef.ComputeIsEven x h_precond := by
  simp only [RPOrig.ComputeIsEven, RPRef.ComputeIsEven]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.ComputeIsEven RPRef.ComputeIsEven; rfl))
