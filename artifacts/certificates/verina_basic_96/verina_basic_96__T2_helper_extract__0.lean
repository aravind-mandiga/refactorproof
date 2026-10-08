-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SwapSimultaneous_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def SwapSimultaneous (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) : Int × Int :=
  (Y, X)
end RPOrig

namespace RPRef
private def SwapSimultaneous__rp_helper_5fb3d255 (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) : Int × Int :=
  (Y, X)

def SwapSimultaneous (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) : Int × Int :=
  SwapSimultaneous__rp_helper_5fb3d255 X Y h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :
    RPOrig.SwapSimultaneous X Y h_precond = RPRef.SwapSimultaneous X Y h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :
    RPOrig.SwapSimultaneous X Y h_precond = RPRef.SwapSimultaneous X Y h_precond := rfl

theorem rp_equiv_delta_rfl (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :
    RPOrig.SwapSimultaneous X Y h_precond = RPRef.SwapSimultaneous X Y h_precond := by
  delta RPOrig.SwapSimultaneous RPRef.SwapSimultaneous RPRef.SwapSimultaneous__rp_helper_5fb3d255
  rfl

theorem rp_equiv_simp_only (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :
    RPOrig.SwapSimultaneous X Y h_precond = RPRef.SwapSimultaneous X Y h_precond := by
  (simp only [RPOrig.SwapSimultaneous, RPRef.SwapSimultaneous, RPRef.SwapSimultaneous__rp_helper_5fb3d255]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapSimultaneous RPRef.SwapSimultaneous RPRef.SwapSimultaneous__rp_helper_5fb3d255; rfl))

theorem rp_equiv_simp (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :
    RPOrig.SwapSimultaneous X Y h_precond = RPRef.SwapSimultaneous X Y h_precond := by
  (simp [RPOrig.SwapSimultaneous, RPRef.SwapSimultaneous, RPRef.SwapSimultaneous__rp_helper_5fb3d255]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapSimultaneous RPRef.SwapSimultaneous RPRef.SwapSimultaneous__rp_helper_5fb3d255; rfl))
