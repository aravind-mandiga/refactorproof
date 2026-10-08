-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findSmallest_precond (s : Array Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def findSmallest (s : Array Nat) (h_precond : findSmallest_precond (s)) : Option Nat :=
  s.toList.min?
end RPOrig

namespace RPRef
private def findSmallest__rp_helper_06efecc0 (s : Array Nat) (h_precond : findSmallest_precond (s)) : Option Nat :=
  s.toList.min?

def findSmallest (s : Array Nat) (h_precond : findSmallest_precond (s)) : Option Nat :=
  findSmallest__rp_helper_06efecc0 s h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : Array Nat) (h_precond : findSmallest_precond (s)) :
    RPOrig.findSmallest s h_precond = RPRef.findSmallest s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : Array Nat) (h_precond : findSmallest_precond (s)) :
    RPOrig.findSmallest s h_precond = RPRef.findSmallest s h_precond := rfl

theorem rp_equiv_delta_rfl (s : Array Nat) (h_precond : findSmallest_precond (s)) :
    RPOrig.findSmallest s h_precond = RPRef.findSmallest s h_precond := by
  delta RPOrig.findSmallest RPRef.findSmallest RPRef.findSmallest__rp_helper_06efecc0
  rfl

theorem rp_equiv_simp_only (s : Array Nat) (h_precond : findSmallest_precond (s)) :
    RPOrig.findSmallest s h_precond = RPRef.findSmallest s h_precond := by
  (simp only [RPOrig.findSmallest, RPRef.findSmallest, RPRef.findSmallest__rp_helper_06efecc0]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findSmallest RPRef.findSmallest RPRef.findSmallest__rp_helper_06efecc0; rfl))

theorem rp_equiv_simp (s : Array Nat) (h_precond : findSmallest_precond (s)) :
    RPOrig.findSmallest s h_precond = RPRef.findSmallest s h_precond := by
  (simp [RPOrig.findSmallest, RPRef.findSmallest, RPRef.findSmallest__rp_helper_06efecc0]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findSmallest RPRef.findSmallest RPRef.findSmallest__rp_helper_06efecc0; rfl))
