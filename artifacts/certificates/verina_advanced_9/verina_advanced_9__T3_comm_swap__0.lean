-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def sumOfDigits (x : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + (n % 10))
  go x 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def countSumDivisibleBy_precond (n : Nat) (d : Nat) : Prop :=
  -- !benchmark @start precond
  d > 0
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def isSumDivisibleBy (x : Nat) (d:Nat) : Bool :=
  (sumOfDigits x) % d = 0

namespace RPOrig

def countSumDivisibleBy (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) : Nat :=
  let rec go (i acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | i'+1 =>
      let acc' := if isSumDivisibleBy i' d then acc + 1 else acc
      go i' acc'
  go n 0
end RPOrig

namespace RPRef

def countSumDivisibleBy (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) : Nat :=
  let rec go (i acc : Nat) : Nat :=
    match i with
    | 0 => acc
    | i'+1 =>
      let acc' := if isSumDivisibleBy i' d then 1 + acc else acc
      go i' acc'
  go n 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    RPOrig.countSumDivisibleBy n d h_precond = RPRef.countSumDivisibleBy n d h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    RPOrig.countSumDivisibleBy n d h_precond = RPRef.countSumDivisibleBy n d h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    RPOrig.countSumDivisibleBy n d h_precond = RPRef.countSumDivisibleBy n d h_precond := by
  delta RPOrig.countSumDivisibleBy RPRef.countSumDivisibleBy RPOrig.countSumDivisibleBy.go RPRef.countSumDivisibleBy.go
  rfl

theorem rp_equiv_simp_only (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    RPOrig.countSumDivisibleBy n d h_precond = RPRef.countSumDivisibleBy n d h_precond := by
  first
    | (simp only [RPOrig.countSumDivisibleBy, RPRef.countSumDivisibleBy, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.countSumDivisibleBy RPRef.countSumDivisibleBy RPOrig.countSumDivisibleBy.go RPRef.countSumDivisibleBy.go; rfl))
    | (simp only [RPOrig.countSumDivisibleBy, RPRef.countSumDivisibleBy, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.countSumDivisibleBy RPRef.countSumDivisibleBy RPOrig.countSumDivisibleBy.go RPRef.countSumDivisibleBy.go; rfl))
    | (simp only [RPOrig.countSumDivisibleBy, RPRef.countSumDivisibleBy, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.countSumDivisibleBy RPRef.countSumDivisibleBy RPOrig.countSumDivisibleBy.go RPRef.countSumDivisibleBy.go; rfl))
    | (simp only [RPOrig.countSumDivisibleBy, RPRef.countSumDivisibleBy]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.countSumDivisibleBy RPRef.countSumDivisibleBy RPOrig.countSumDivisibleBy.go RPRef.countSumDivisibleBy.go; rfl))

theorem rp_equiv_simp (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    RPOrig.countSumDivisibleBy n d h_precond = RPRef.countSumDivisibleBy n d h_precond := by
  first
    | (simp [RPOrig.countSumDivisibleBy, RPRef.countSumDivisibleBy, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.countSumDivisibleBy RPRef.countSumDivisibleBy RPOrig.countSumDivisibleBy.go RPRef.countSumDivisibleBy.go; rfl))
    | (simp [RPOrig.countSumDivisibleBy, RPRef.countSumDivisibleBy, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.countSumDivisibleBy RPRef.countSumDivisibleBy RPOrig.countSumDivisibleBy.go RPRef.countSumDivisibleBy.go; rfl))
    | (simp [RPOrig.countSumDivisibleBy, RPRef.countSumDivisibleBy, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.countSumDivisibleBy RPRef.countSumDivisibleBy RPOrig.countSumDivisibleBy.go RPRef.countSumDivisibleBy.go; rfl))
    | (simp [RPOrig.countSumDivisibleBy, RPRef.countSumDivisibleBy]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.countSumDivisibleBy RPRef.countSumDivisibleBy RPOrig.countSumDivisibleBy.go RPRef.countSumDivisibleBy.go; rfl))

theorem rp_equiv_ac_rfl (n : Nat) (d : Nat) (h_precond : countSumDivisibleBy_precond (n) (d)) :
    RPOrig.countSumDivisibleBy n d h_precond = RPRef.countSumDivisibleBy n d h_precond := by
  (try simp only [RPOrig.countSumDivisibleBy, RPRef.countSumDivisibleBy]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.countSumDivisibleBy RPRef.countSumDivisibleBy RPOrig.countSumDivisibleBy.go RPRef.countSumDivisibleBy.go; rfl))
