-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def MoveZeroesToEnd_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def MoveZeroesToEnd (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) : Array Int :=
  let nonZeros := arr.toList.filter (· ≠ 0)
  let zeros := arr.toList.filter (· = 0)
  Array.mk (nonZeros ++ zeros)
end RPOrig

namespace RPRef
private def MoveZeroesToEnd__rp_helper_72855865 (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) : Array Int :=
  let nonZeros := arr.toList.filter (· ≠ 0)
  let zeros := arr.toList.filter (· = 0)
  Array.mk (nonZeros ++ zeros)

def MoveZeroesToEnd (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) : Array Int :=
  MoveZeroesToEnd__rp_helper_72855865 arr h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :
    RPOrig.MoveZeroesToEnd arr h_precond = RPRef.MoveZeroesToEnd arr h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :
    RPOrig.MoveZeroesToEnd arr h_precond = RPRef.MoveZeroesToEnd arr h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :
    RPOrig.MoveZeroesToEnd arr h_precond = RPRef.MoveZeroesToEnd arr h_precond := by
  delta RPOrig.MoveZeroesToEnd RPRef.MoveZeroesToEnd RPRef.MoveZeroesToEnd__rp_helper_72855865
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :
    RPOrig.MoveZeroesToEnd arr h_precond = RPRef.MoveZeroesToEnd arr h_precond := by
  (simp only [RPOrig.MoveZeroesToEnd, RPRef.MoveZeroesToEnd, RPRef.MoveZeroesToEnd__rp_helper_72855865]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.MoveZeroesToEnd RPRef.MoveZeroesToEnd RPRef.MoveZeroesToEnd__rp_helper_72855865; rfl))

theorem rp_equiv_simp (arr : Array Int) (h_precond : MoveZeroesToEnd_precond (arr)) :
    RPOrig.MoveZeroesToEnd arr h_precond = RPRef.MoveZeroesToEnd arr h_precond := by
  (simp [RPOrig.MoveZeroesToEnd, RPRef.MoveZeroesToEnd, RPRef.MoveZeroesToEnd__rp_helper_72855865]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.MoveZeroesToEnd RPRef.MoveZeroesToEnd RPRef.MoveZeroesToEnd__rp_helper_72855865; rfl))
