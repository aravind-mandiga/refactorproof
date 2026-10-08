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
private def Abs__rp_branch_c6672445 (x : Int) (h_precond : Abs_precond (x)) : Int :=
  x

def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  if x < 0 then -x else
    Abs__rp_branch_c6672445 x h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (x : Int) (h_precond : Abs_precond (x)) :
    RPOrig.Abs x h_precond = RPRef.Abs x h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (x : Int) (h_precond : Abs_precond (x)) :
    RPOrig.Abs x h_precond = RPRef.Abs x h_precond := rfl

theorem rp_equiv_delta_rfl (x : Int) (h_precond : Abs_precond (x)) :
    RPOrig.Abs x h_precond = RPRef.Abs x h_precond := by
  first
    | (delta RPOrig.Abs RPRef.Abs RPRef.Abs__rp_branch_c6672445; rfl)
    | (delta RPOrig.Abs RPRef.Abs RPRef.Abs__rp_branch_c6672445 RPOrig.Abs._unary; rfl)
    | (set_option smartUnfolding false in rfl)

theorem rp_equiv_simp_only (x : Int) (h_precond : Abs_precond (x)) :
    RPOrig.Abs x h_precond = RPRef.Abs x h_precond := by
  (simp only [RPOrig.Abs, RPRef.Abs, RPRef.Abs__rp_branch_c6672445]) <;> (first | rfl | (delta RPOrig.Abs RPRef.Abs RPRef.Abs__rp_branch_c6672445; rfl) | (delta RPOrig.Abs RPRef.Abs RPRef.Abs__rp_branch_c6672445 RPOrig.Abs._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_simp (x : Int) (h_precond : Abs_precond (x)) :
    RPOrig.Abs x h_precond = RPRef.Abs x h_precond := by
  (simp [RPOrig.Abs, RPRef.Abs, RPRef.Abs__rp_branch_c6672445]) <;> (first | rfl | (delta RPOrig.Abs RPRef.Abs RPRef.Abs__rp_branch_c6672445; rfl) | (delta RPOrig.Abs RPRef.Abs RPRef.Abs__rp_branch_c6672445 RPOrig.Abs._unary; rfl) | (set_option smartUnfolding false in rfl))
