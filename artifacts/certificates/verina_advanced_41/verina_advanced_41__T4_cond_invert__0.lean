-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  if a >= b && a >= c then a
  else if b >= a && b >= c then b
  else c
end RPOrig

namespace RPRef

def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  if ¬ (a >= b && a >= c) then if b >= a && b >= c then b
  else c
  else a
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    RPOrig.maxOfThree a b c h_precond = RPRef.maxOfThree a b c h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    RPOrig.maxOfThree a b c h_precond = RPRef.maxOfThree a b c h_precond := rfl

theorem rp_equiv_delta_rfl (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    RPOrig.maxOfThree a b c h_precond = RPRef.maxOfThree a b c h_precond := by
  delta RPOrig.maxOfThree RPRef.maxOfThree
  rfl

theorem rp_equiv_simp_only (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    RPOrig.maxOfThree a b c h_precond = RPRef.maxOfThree a b c h_precond := by
  first
    | (simp only [RPOrig.maxOfThree, RPRef.maxOfThree, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxOfThree RPRef.maxOfThree; rfl))
    | (simp only [RPOrig.maxOfThree, RPRef.maxOfThree, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxOfThree RPRef.maxOfThree; rfl))
    | (simp only [RPOrig.maxOfThree, RPRef.maxOfThree]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxOfThree RPRef.maxOfThree; rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    RPOrig.maxOfThree a b c h_precond = RPRef.maxOfThree a b c h_precond := by
  first
    | (simp [RPOrig.maxOfThree, RPRef.maxOfThree, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxOfThree RPRef.maxOfThree; rfl))
    | (simp [RPOrig.maxOfThree, RPRef.maxOfThree, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxOfThree RPRef.maxOfThree; rfl))
    | (simp [RPOrig.maxOfThree, RPRef.maxOfThree]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxOfThree RPRef.maxOfThree; rfl))

theorem rp_equiv_bycases (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    RPOrig.maxOfThree a b c h_precond = RPRef.maxOfThree a b c h_precond := by
  by_cases h : (a >= b && a >= c) <;> (try simp [h, RPOrig.maxOfThree, RPRef.maxOfThree]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxOfThree RPRef.maxOfThree; rfl))

theorem rp_equiv_bycases_ite (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    RPOrig.maxOfThree a b c h_precond = RPRef.maxOfThree a b c h_precond := by
  by_cases h : (a >= b && a >= c) <;> (try simp [h, ite_not, RPOrig.maxOfThree, RPRef.maxOfThree]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxOfThree RPRef.maxOfThree; rfl))

theorem rp_equiv_split_simp_all (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    RPOrig.maxOfThree a b c h_precond = RPRef.maxOfThree a b c h_precond := by
  simp only [RPOrig.maxOfThree, RPRef.maxOfThree]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxOfThree RPRef.maxOfThree; rfl))
