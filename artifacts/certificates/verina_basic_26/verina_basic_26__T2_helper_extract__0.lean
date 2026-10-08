-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isEven_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def isEven (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  n % 2 == 0
end RPOrig

namespace RPRef
private def isEven__rp_helper_3a986bdd (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  n % 2 == 0

def isEven (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  isEven__rp_helper_3a986bdd n h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Int) (h_precond : isEven_precond (n)) :
    RPOrig.isEven n h_precond = RPRef.isEven n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Int) (h_precond : isEven_precond (n)) :
    RPOrig.isEven n h_precond = RPRef.isEven n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Int) (h_precond : isEven_precond (n)) :
    RPOrig.isEven n h_precond = RPRef.isEven n h_precond := by
  delta RPOrig.isEven RPRef.isEven RPRef.isEven__rp_helper_3a986bdd
  rfl

theorem rp_equiv_simp_only (n : Int) (h_precond : isEven_precond (n)) :
    RPOrig.isEven n h_precond = RPRef.isEven n h_precond := by
  (simp only [RPOrig.isEven, RPRef.isEven, RPRef.isEven__rp_helper_3a986bdd]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isEven RPRef.isEven RPRef.isEven__rp_helper_3a986bdd; rfl))

theorem rp_equiv_simp (n : Int) (h_precond : isEven_precond (n)) :
    RPOrig.isEven n h_precond = RPRef.isEven n h_precond := by
  (simp [RPOrig.isEven, RPRef.isEven, RPRef.isEven__rp_helper_3a986bdd]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isEven RPRef.isEven RPRef.isEven__rp_helper_3a986bdd; rfl))
