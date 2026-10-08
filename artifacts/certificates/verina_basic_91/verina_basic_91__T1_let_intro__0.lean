-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Swap_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def Swap (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) : Int × Int :=
  let x := X
  let y := Y
  let tmp := x
  let x := y
  let y := tmp
  (x, y)
end RPOrig

namespace RPRef

def Swap (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) : Int × Int :=
  let __rp_tmp_ed7c8607 : Int × Int :=
    let x := X
    let y := Y
    let tmp := x
    let x := y
    let y := tmp
    (x, y)
  __rp_tmp_ed7c8607
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) :
    RPOrig.Swap X Y h_precond = RPRef.Swap X Y h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) :
    RPOrig.Swap X Y h_precond = RPRef.Swap X Y h_precond := rfl

theorem rp_equiv_delta_rfl (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) :
    RPOrig.Swap X Y h_precond = RPRef.Swap X Y h_precond := by
  delta RPOrig.Swap RPRef.Swap
  rfl

theorem rp_equiv_simp_only (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) :
    RPOrig.Swap X Y h_precond = RPRef.Swap X Y h_precond := by
  (simp only [RPOrig.Swap, RPRef.Swap]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Swap RPRef.Swap; rfl))

theorem rp_equiv_simp (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) :
    RPOrig.Swap X Y h_precond = RPRef.Swap X Y h_precond := by
  (simp [RPOrig.Swap, RPRef.Swap]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Swap RPRef.Swap; rfl))
