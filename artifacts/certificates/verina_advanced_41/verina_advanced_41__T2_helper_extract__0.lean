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
private def maxOfThree__rp_helper_7c6c6d3d (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  if a >= b && a >= c then a
  else if b >= a && b >= c then b
  else c

def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  maxOfThree__rp_helper_7c6c6d3d a b c h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    RPOrig.maxOfThree a b c h_precond = RPRef.maxOfThree a b c h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    RPOrig.maxOfThree a b c h_precond = RPRef.maxOfThree a b c h_precond := rfl

theorem rp_equiv_delta_rfl (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    RPOrig.maxOfThree a b c h_precond = RPRef.maxOfThree a b c h_precond := by
  delta RPOrig.maxOfThree RPRef.maxOfThree RPRef.maxOfThree__rp_helper_7c6c6d3d
  rfl

theorem rp_equiv_simp_only (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    RPOrig.maxOfThree a b c h_precond = RPRef.maxOfThree a b c h_precond := by
  (simp only [RPOrig.maxOfThree, RPRef.maxOfThree, RPRef.maxOfThree__rp_helper_7c6c6d3d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxOfThree RPRef.maxOfThree RPRef.maxOfThree__rp_helper_7c6c6d3d; rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    RPOrig.maxOfThree a b c h_precond = RPRef.maxOfThree a b c h_precond := by
  (simp [RPOrig.maxOfThree, RPRef.maxOfThree, RPRef.maxOfThree__rp_helper_7c6c6d3d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxOfThree RPRef.maxOfThree RPRef.maxOfThree__rp_helper_7c6c6d3d; rfl))
