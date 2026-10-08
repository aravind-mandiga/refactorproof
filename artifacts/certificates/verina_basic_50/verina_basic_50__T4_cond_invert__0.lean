-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Abs_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  if x < 0 then -x else x
end RPOrig

namespace RPRef

def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  if ¬ (x < 0) then x
  else -x
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (x : Int) (h_precond : Abs_precond (x)) :
    RPOrig.Abs x h_precond = RPRef.Abs x h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (x : Int) (h_precond : Abs_precond (x)) :
    RPOrig.Abs x h_precond = RPRef.Abs x h_precond := rfl

theorem rp_equiv_delta_rfl (x : Int) (h_precond : Abs_precond (x)) :
    RPOrig.Abs x h_precond = RPRef.Abs x h_precond := by
  delta RPOrig.Abs RPRef.Abs
  rfl

theorem rp_equiv_simp_only (x : Int) (h_precond : Abs_precond (x)) :
    RPOrig.Abs x h_precond = RPRef.Abs x h_precond := by
  first
    | (simp only [RPOrig.Abs, RPRef.Abs, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Abs RPRef.Abs; rfl))
    | (simp only [RPOrig.Abs, RPRef.Abs, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Abs RPRef.Abs; rfl))
    | (simp only [RPOrig.Abs, RPRef.Abs]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Abs RPRef.Abs; rfl))

theorem rp_equiv_simp (x : Int) (h_precond : Abs_precond (x)) :
    RPOrig.Abs x h_precond = RPRef.Abs x h_precond := by
  first
    | (simp [RPOrig.Abs, RPRef.Abs, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Abs RPRef.Abs; rfl))
    | (simp [RPOrig.Abs, RPRef.Abs, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Abs RPRef.Abs; rfl))
    | (simp [RPOrig.Abs, RPRef.Abs]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Abs RPRef.Abs; rfl))

theorem rp_equiv_bycases (x : Int) (h_precond : Abs_precond (x)) :
    RPOrig.Abs x h_precond = RPRef.Abs x h_precond := by
  by_cases h : (x < 0) <;> (try simp [h, RPOrig.Abs, RPRef.Abs]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Abs RPRef.Abs; rfl))

theorem rp_equiv_bycases_ite (x : Int) (h_precond : Abs_precond (x)) :
    RPOrig.Abs x h_precond = RPRef.Abs x h_precond := by
  by_cases h : (x < 0) <;> (try simp [h, ite_not, RPOrig.Abs, RPRef.Abs]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Abs RPRef.Abs; rfl))

theorem rp_equiv_split_simp_all (x : Int) (h_precond : Abs_precond (x)) :
    RPOrig.Abs x h_precond = RPRef.Abs x h_precond := by
  simp only [RPOrig.Abs, RPRef.Abs]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Abs RPRef.Abs; rfl))
