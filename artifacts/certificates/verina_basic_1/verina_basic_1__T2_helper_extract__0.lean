-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def hasOppositeSign_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def hasOppositeSign (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  a * b < 0
end RPOrig

namespace RPRef
private def hasOppositeSign__rp_helper_5272bffb (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  a * b < 0

def hasOppositeSign (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  hasOppositeSign__rp_helper_5272bffb a b h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    RPOrig.hasOppositeSign a b h_precond = RPRef.hasOppositeSign a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    RPOrig.hasOppositeSign a b h_precond = RPRef.hasOppositeSign a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    RPOrig.hasOppositeSign a b h_precond = RPRef.hasOppositeSign a b h_precond := by
  delta RPOrig.hasOppositeSign RPRef.hasOppositeSign RPRef.hasOppositeSign__rp_helper_5272bffb
  rfl

theorem rp_equiv_simp_only (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    RPOrig.hasOppositeSign a b h_precond = RPRef.hasOppositeSign a b h_precond := by
  (simp only [RPOrig.hasOppositeSign, RPRef.hasOppositeSign, RPRef.hasOppositeSign__rp_helper_5272bffb]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOppositeSign RPRef.hasOppositeSign RPRef.hasOppositeSign__rp_helper_5272bffb; rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    RPOrig.hasOppositeSign a b h_precond = RPRef.hasOppositeSign a b h_precond := by
  (simp [RPOrig.hasOppositeSign, RPRef.hasOppositeSign, RPRef.hasOppositeSign__rp_helper_5272bffb]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOppositeSign RPRef.hasOppositeSign RPRef.hasOppositeSign__rp_helper_5272bffb; rfl))
