-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def DivisionFunction_precond (x : Nat) (y : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def divMod (x y : Nat) : Int × Int :=
  let q : Int := Int.ofNat (x / y)
  let r : Int := Int.ofNat (x % y)
  (r, q)

namespace RPOrig

def DivisionFunction (x : Nat) (y : Nat) (h_precond : DivisionFunction_precond (x) (y)) : Int × Int :=
  if y = 0 then (Int.ofNat x, 0) else divMod x y
end RPOrig

namespace RPRef

private def DivisionFunction__rp_helper_e90423eb (x : Nat) (y : Nat) (h_precond : DivisionFunction_precond (x) (y)) : Int × Int :=
  if y = 0 then (Int.ofNat x, 0) else divMod x y

def DivisionFunction (x : Nat) (y : Nat) (h_precond : DivisionFunction_precond (x) (y)) : Int × Int :=
  DivisionFunction__rp_helper_e90423eb x y h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (x : Nat) (y : Nat) (h_precond : DivisionFunction_precond (x) (y)) :
    RPOrig.DivisionFunction x y h_precond = RPRef.DivisionFunction x y h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (x : Nat) (y : Nat) (h_precond : DivisionFunction_precond (x) (y)) :
    RPOrig.DivisionFunction x y h_precond = RPRef.DivisionFunction x y h_precond := rfl

theorem rp_equiv_delta_rfl (x : Nat) (y : Nat) (h_precond : DivisionFunction_precond (x) (y)) :
    RPOrig.DivisionFunction x y h_precond = RPRef.DivisionFunction x y h_precond := by
  delta RPOrig.DivisionFunction RPRef.DivisionFunction RPRef.DivisionFunction__rp_helper_e90423eb
  rfl

theorem rp_equiv_simp_only (x : Nat) (y : Nat) (h_precond : DivisionFunction_precond (x) (y)) :
    RPOrig.DivisionFunction x y h_precond = RPRef.DivisionFunction x y h_precond := by
  (simp only [RPOrig.DivisionFunction, RPRef.DivisionFunction, RPRef.DivisionFunction__rp_helper_e90423eb]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.DivisionFunction RPRef.DivisionFunction RPRef.DivisionFunction__rp_helper_e90423eb; rfl))

theorem rp_equiv_simp (x : Nat) (y : Nat) (h_precond : DivisionFunction_precond (x) (y)) :
    RPOrig.DivisionFunction x y h_precond = RPRef.DivisionFunction x y h_precond := by
  (simp [RPOrig.DivisionFunction, RPRef.DivisionFunction, RPRef.DivisionFunction__rp_helper_e90423eb]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.DivisionFunction RPRef.DivisionFunction RPRef.DivisionFunction__rp_helper_e90423eb; rfl))
