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
  let __rp_tmp_fdb5d16f : Int :=
    if a <= b && a <= c then a
    else if b <= a && b <= c then b
    else c
  __rp_tmp_fdb5d16f
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
  (simp only [RPOrig.minOfThree, RPRef.minOfThree]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minOfThree RPRef.minOfThree; rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    RPOrig.minOfThree a b c h_precond = RPRef.minOfThree a b c h_precond := by
  (simp [RPOrig.minOfThree, RPRef.minOfThree]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minOfThree RPRef.minOfThree; rfl))
