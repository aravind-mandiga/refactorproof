-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def minOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def minOfThree (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  if a <= b && a <= c then a
  else if b <= a && b <= c then b
  else c
end RPOrig

namespace RPRef

def minOfThree (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  if ¬ (a <= b && a <= c) then if b <= a && b <= c then b
  else c
  else a
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    RPOrig.minOfThree a b c h_precond = RPRef.minOfThree a b c h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    RPOrig.minOfThree a b c h_precond = RPRef.minOfThree a b c h_precond := rfl

theorem rp_equiv_delta_rfl (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    RPOrig.minOfThree a b c h_precond = RPRef.minOfThree a b c h_precond := by
  delta RPOrig.minOfThree RPRef.minOfThree
  rfl

theorem rp_equiv_simp_only (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    RPOrig.minOfThree a b c h_precond = RPRef.minOfThree a b c h_precond := by
  first
    | (simp only [RPOrig.minOfThree, RPRef.minOfThree, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minOfThree RPRef.minOfThree; rfl))
    | (simp only [RPOrig.minOfThree, RPRef.minOfThree, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minOfThree RPRef.minOfThree; rfl))
    | (simp only [RPOrig.minOfThree, RPRef.minOfThree]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minOfThree RPRef.minOfThree; rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    RPOrig.minOfThree a b c h_precond = RPRef.minOfThree a b c h_precond := by
  first
    | (simp [RPOrig.minOfThree, RPRef.minOfThree, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minOfThree RPRef.minOfThree; rfl))
    | (simp [RPOrig.minOfThree, RPRef.minOfThree, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minOfThree RPRef.minOfThree; rfl))
    | (simp [RPOrig.minOfThree, RPRef.minOfThree]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minOfThree RPRef.minOfThree; rfl))

theorem rp_equiv_bycases (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    RPOrig.minOfThree a b c h_precond = RPRef.minOfThree a b c h_precond := by
  by_cases h : (a <= b && a <= c) <;> (try simp [h, RPOrig.minOfThree, RPRef.minOfThree]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minOfThree RPRef.minOfThree; rfl))

theorem rp_equiv_bycases_ite (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    RPOrig.minOfThree a b c h_precond = RPRef.minOfThree a b c h_precond := by
  by_cases h : (a <= b && a <= c) <;> (try simp [h, ite_not, RPOrig.minOfThree, RPRef.minOfThree]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minOfThree RPRef.minOfThree; rfl))

theorem rp_equiv_split_simp_all (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    RPOrig.minOfThree a b c h_precond = RPRef.minOfThree a b c h_precond := by
  simp only [RPOrig.minOfThree, RPRef.minOfThree]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minOfThree RPRef.minOfThree; rfl))
