-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isPerfectSquare_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def isPerfectSquare (n : Nat) : Bool :=
  if n = 0 then true
  else
    let rec check (x : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel + 1 =>
        if x * x > n then false
        else if x * x = n then true
        else check (x + 1) fuel
    check 1 n
end RPOrig

namespace RPRef
private def isPerfectSquare__rp_helper_521a2256 (n : Nat) : Bool :=
  if n = 0 then true
  else
    let rec check (x : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel + 1 =>
        if x * x > n then false
        else if x * x = n then true
        else check (x + 1) fuel
    check 1 n

def isPerfectSquare (n : Nat) : Bool :=
  isPerfectSquare__rp_helper_521a2256 n
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := rfl

theorem rp_equiv_delta_rfl (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := by
  delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPRef.isPerfectSquare__rp_helper_521a2256 RPOrig.isPerfectSquare.check RPRef.isPerfectSquare__rp_helper_521a2256.check
  rfl

theorem rp_equiv_simp_only (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := by
  (simp only [RPOrig.isPerfectSquare, RPRef.isPerfectSquare, RPRef.isPerfectSquare__rp_helper_521a2256]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPRef.isPerfectSquare__rp_helper_521a2256 RPOrig.isPerfectSquare.check RPRef.isPerfectSquare__rp_helper_521a2256.check; rfl))

theorem rp_equiv_simp (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := by
  (simp [RPOrig.isPerfectSquare, RPRef.isPerfectSquare, RPRef.isPerfectSquare__rp_helper_521a2256]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPRef.isPerfectSquare__rp_helper_521a2256 RPOrig.isPerfectSquare.check RPRef.isPerfectSquare__rp_helper_521a2256.check; rfl))
