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

def isPerfectSquare (n : Nat) : Bool :=
  if n = 0 then true
  else
    let rec check (x : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel + 1 =>
        if x * x > n then false
        else if x * x = n then true
        else check (1 + x) fuel
    check 1 n
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := rfl

theorem rp_equiv_delta_rfl (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := by
  delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check
  rfl

theorem rp_equiv_simp_only (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := by
  first
    | (simp only [RPOrig.isPerfectSquare, RPRef.isPerfectSquare, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))
    | (simp only [RPOrig.isPerfectSquare, RPRef.isPerfectSquare, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))
    | (simp only [RPOrig.isPerfectSquare, RPRef.isPerfectSquare, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))
    | (simp only [RPOrig.isPerfectSquare, RPRef.isPerfectSquare]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))

theorem rp_equiv_simp (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := by
  first
    | (simp [RPOrig.isPerfectSquare, RPRef.isPerfectSquare, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))
    | (simp [RPOrig.isPerfectSquare, RPRef.isPerfectSquare, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))
    | (simp [RPOrig.isPerfectSquare, RPRef.isPerfectSquare, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))
    | (simp [RPOrig.isPerfectSquare, RPRef.isPerfectSquare]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))

theorem rp_equiv_ac_rfl (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := by
  (try simp only [RPOrig.isPerfectSquare, RPRef.isPerfectSquare]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))
