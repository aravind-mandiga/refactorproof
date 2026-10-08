-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SwapArithmetic_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def SwapArithmetic (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  let x1 := X
  let y1 := Y
  let x2 := y1 - x1
  let y2 := y1 - x2
  let x3 := y2 + x2
  (x3, y2)
end RPOrig

namespace RPRef
private def SwapArithmetic__rp_helper_2265221a (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  let x1 := X
  let y1 := Y
  let x2 := y1 - x1
  let y2 := y1 - x2
  let x3 := y2 + x2
  (x3, y2)

def SwapArithmetic (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  SwapArithmetic__rp_helper_2265221a X Y h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    RPOrig.SwapArithmetic X Y h_precond = RPRef.SwapArithmetic X Y h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    RPOrig.SwapArithmetic X Y h_precond = RPRef.SwapArithmetic X Y h_precond := rfl

theorem rp_equiv_delta_rfl (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    RPOrig.SwapArithmetic X Y h_precond = RPRef.SwapArithmetic X Y h_precond := by
  delta RPOrig.SwapArithmetic RPRef.SwapArithmetic RPRef.SwapArithmetic__rp_helper_2265221a
  rfl

theorem rp_equiv_simp_only (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    RPOrig.SwapArithmetic X Y h_precond = RPRef.SwapArithmetic X Y h_precond := by
  (simp only [RPOrig.SwapArithmetic, RPRef.SwapArithmetic, RPRef.SwapArithmetic__rp_helper_2265221a]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapArithmetic RPRef.SwapArithmetic RPRef.SwapArithmetic__rp_helper_2265221a; rfl))

theorem rp_equiv_simp (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    RPOrig.SwapArithmetic X Y h_precond = RPRef.SwapArithmetic X Y h_precond := by
  (simp [RPOrig.SwapArithmetic, RPRef.SwapArithmetic, RPRef.SwapArithmetic__rp_helper_2265221a]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SwapArithmetic RPRef.SwapArithmetic RPRef.SwapArithmetic__rp_helper_2265221a; rfl))
