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

def hasOppositeSign (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  let __rp_tmp_8c14b1b6 : Bool :=
    a * b < 0
  __rp_tmp_8c14b1b6
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    RPOrig.hasOppositeSign a b h_precond = RPRef.hasOppositeSign a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    RPOrig.hasOppositeSign a b h_precond = RPRef.hasOppositeSign a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    RPOrig.hasOppositeSign a b h_precond = RPRef.hasOppositeSign a b h_precond := by
  delta RPOrig.hasOppositeSign RPRef.hasOppositeSign
  rfl

theorem rp_equiv_simp_only (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    RPOrig.hasOppositeSign a b h_precond = RPRef.hasOppositeSign a b h_precond := by
  (simp only [RPOrig.hasOppositeSign, RPRef.hasOppositeSign]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOppositeSign RPRef.hasOppositeSign; rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    RPOrig.hasOppositeSign a b h_precond = RPRef.hasOppositeSign a b h_precond := by
  (simp [RPOrig.hasOppositeSign, RPRef.hasOppositeSign]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOppositeSign RPRef.hasOppositeSign; rfl))
