-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def rotate_precond (a : Array Int) (offset : Int) : Prop :=
  -- !benchmark @start precond
  offset ≥ 0
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def rotateAux (a : Array Int) (offset : Int) (i : Nat) (len : Nat) (b : Array Int) : Array Int :=
  if i < len then
    let idx_int : Int := (Int.ofNat i + offset) % (Int.ofNat len)
    let idx_int_adjusted := if idx_int < 0 then idx_int + Int.ofNat len else idx_int
    let idx_nat : Nat := Int.toNat idx_int_adjusted
    let new_b := b.set! i (a[idx_nat]!)
    rotateAux a offset (i + 1) len new_b
  else b

namespace RPOrig

def rotate (a : Array Int) (offset : Int) (h_precond : rotate_precond (a) (offset)) : Array Int :=
  let len := a.size
  let default_val : Int := if len > 0 then a[0]! else 0
  let b0 := Array.mkArray len default_val
  rotateAux a offset 0 len b0
end RPOrig

namespace RPRef

private def rotate__rp_helper_601d1c2a (a : Array Int) (offset : Int) (h_precond : rotate_precond (a) (offset)) : Array Int :=
  let len := a.size
  let default_val : Int := if len > 0 then a[0]! else 0
  let b0 := Array.mkArray len default_val
  rotateAux a offset 0 len b0

def rotate (a : Array Int) (offset : Int) (h_precond : rotate_precond (a) (offset)) : Array Int :=
  rotate__rp_helper_601d1c2a a offset h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (offset : Int) (h_precond : rotate_precond (a) (offset)) :
    RPOrig.rotate a offset h_precond = RPRef.rotate a offset h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (offset : Int) (h_precond : rotate_precond (a) (offset)) :
    RPOrig.rotate a offset h_precond = RPRef.rotate a offset h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (offset : Int) (h_precond : rotate_precond (a) (offset)) :
    RPOrig.rotate a offset h_precond = RPRef.rotate a offset h_precond := by
  delta RPOrig.rotate RPRef.rotate RPRef.rotate__rp_helper_601d1c2a
  rfl

theorem rp_equiv_simp_only (a : Array Int) (offset : Int) (h_precond : rotate_precond (a) (offset)) :
    RPOrig.rotate a offset h_precond = RPRef.rotate a offset h_precond := by
  (simp only [RPOrig.rotate, RPRef.rotate, RPRef.rotate__rp_helper_601d1c2a]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rotate RPRef.rotate RPRef.rotate__rp_helper_601d1c2a; rfl))

theorem rp_equiv_simp (a : Array Int) (offset : Int) (h_precond : rotate_precond (a) (offset)) :
    RPOrig.rotate a offset h_precond = RPRef.rotate a offset h_precond := by
  (simp [RPOrig.rotate, RPRef.rotate, RPRef.rotate__rp_helper_601d1c2a]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rotate RPRef.rotate RPRef.rotate__rp_helper_601d1c2a; rfl))
