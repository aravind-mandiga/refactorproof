-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def hasCommonElement_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧ b.size > 0
  -- !benchmark @end precond



namespace RPOrig

def hasCommonElement (a : Array Int) (b : Array Int) (h_precond : hasCommonElement_precond (a) (b)) : Bool :=
  a.any fun x => b.any fun y => x = y
end RPOrig

namespace RPRef

def hasCommonElement (a : Array Int) (b : Array Int) (h_precond : hasCommonElement_precond (a) (b)) : Bool :=
  let __rp_tmp_e9bca06a : Bool :=
    a.any fun x => b.any fun y => x = y
  __rp_tmp_e9bca06a
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (b : Array Int) (h_precond : hasCommonElement_precond (a) (b)) :
    RPOrig.hasCommonElement a b h_precond = RPRef.hasCommonElement a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (b : Array Int) (h_precond : hasCommonElement_precond (a) (b)) :
    RPOrig.hasCommonElement a b h_precond = RPRef.hasCommonElement a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (b : Array Int) (h_precond : hasCommonElement_precond (a) (b)) :
    RPOrig.hasCommonElement a b h_precond = RPRef.hasCommonElement a b h_precond := by
  delta RPOrig.hasCommonElement RPRef.hasCommonElement
  rfl

theorem rp_equiv_simp_only (a : Array Int) (b : Array Int) (h_precond : hasCommonElement_precond (a) (b)) :
    RPOrig.hasCommonElement a b h_precond = RPRef.hasCommonElement a b h_precond := by
  (simp only [RPOrig.hasCommonElement, RPRef.hasCommonElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasCommonElement RPRef.hasCommonElement; rfl))

theorem rp_equiv_simp (a : Array Int) (b : Array Int) (h_precond : hasCommonElement_precond (a) (b)) :
    RPOrig.hasCommonElement a b h_precond = RPRef.hasCommonElement a b h_precond := by
  (simp [RPOrig.hasCommonElement, RPRef.hasCommonElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasCommonElement RPRef.hasCommonElement; rfl))
