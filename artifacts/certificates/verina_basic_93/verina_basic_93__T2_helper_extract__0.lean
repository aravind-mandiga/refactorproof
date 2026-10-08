-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SwapBitvectors_precond (X : UInt8) (Y : UInt8) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def SwapBitvectors (X : UInt8) (Y : UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) : UInt8 × UInt8 :=
  let temp := X.xor Y
  let newY := temp.xor Y
  let newX := temp.xor newY
  (newX, newY)
end RPOrig

namespace RPRef
private def SwapBitvectors__rp_helper_ccb3ec74 (X : UInt8) (Y : UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) : UInt8 × UInt8 :=
  let temp := X.xor Y
  let newY := temp.xor Y
  let newX := temp.xor newY
  (newX, newY)

def SwapBitvectors (X : UInt8) (Y : UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) : UInt8 × UInt8 :=
  SwapBitvectors__rp_helper_ccb3ec74 X Y h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (X : UInt8) (Y : UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) :
    RPOrig.SwapBitvectors X Y h_precond = RPRef.SwapBitvectors X Y h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (X : UInt8) (Y : UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) :
    RPOrig.SwapBitvectors X Y h_precond = RPRef.SwapBitvectors X Y h_precond := rfl

theorem rp_equiv_delta_rfl (X : UInt8) (Y : UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) :
    RPOrig.SwapBitvectors X Y h_precond = RPRef.SwapBitvectors X Y h_precond := by
  delta RPOrig.SwapBitvectors RPRef.SwapBitvectors RPRef.SwapBitvectors__rp_helper_ccb3ec74
  rfl

theorem rp_equiv_simp_only (X : UInt8) (Y : UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) :
    RPOrig.SwapBitvectors X Y h_precond = RPRef.SwapBitvectors X Y h_precond := by
  (simp only [RPOrig.SwapBitvectors, RPRef.SwapBitvectors, RPRef.SwapBitvectors__rp_helper_ccb3ec74]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapBitvectors RPRef.SwapBitvectors RPRef.SwapBitvectors__rp_helper_ccb3ec74; rfl))

theorem rp_equiv_simp (X : UInt8) (Y : UInt8) (h_precond : SwapBitvectors_precond (X) (Y)) :
    RPOrig.SwapBitvectors X Y h_precond = RPRef.SwapBitvectors X Y h_precond := by
  (simp [RPOrig.SwapBitvectors, RPRef.SwapBitvectors, RPRef.SwapBitvectors__rp_helper_ccb3ec74]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapBitvectors RPRef.SwapBitvectors RPRef.SwapBitvectors__rp_helper_ccb3ec74; rfl))
