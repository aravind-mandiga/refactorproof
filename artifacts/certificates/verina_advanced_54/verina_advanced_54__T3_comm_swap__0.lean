-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def missingNumber_precond (nums : List Nat) : Prop :=
  -- !benchmark @start precond
  nums.all (fun x => x ≤ nums.length) ∧ List.Nodup nums
  -- !benchmark @end precond



namespace RPOrig

def missingNumber (nums : List Nat) (h_precond : missingNumber_precond (nums)) : Nat :=
  let n := nums.length
  let expectedSum := (n * (n + 1)) / 2
  let actualSum := nums.foldl (· + ·) 0
  expectedSum - actualSum
end RPOrig

namespace RPRef

def missingNumber (nums : List Nat) (h_precond : missingNumber_precond (nums)) : Nat :=
  let n := nums.length
  let expectedSum := ((n + 1) * n) / 2
  let actualSum := nums.foldl (· + ·) 0
  expectedSum - actualSum
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Nat) (h_precond : missingNumber_precond (nums)) :
    RPOrig.missingNumber nums h_precond = RPRef.missingNumber nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Nat) (h_precond : missingNumber_precond (nums)) :
    RPOrig.missingNumber nums h_precond = RPRef.missingNumber nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Nat) (h_precond : missingNumber_precond (nums)) :
    RPOrig.missingNumber nums h_precond = RPRef.missingNumber nums h_precond := by
  delta RPOrig.missingNumber RPRef.missingNumber
  rfl

theorem rp_equiv_simp_only (nums : List Nat) (h_precond : missingNumber_precond (nums)) :
    RPOrig.missingNumber nums h_precond = RPRef.missingNumber nums h_precond := by
  first
    | (simp only [RPOrig.missingNumber, RPRef.missingNumber, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.missingNumber RPRef.missingNumber; rfl))
    | (simp only [RPOrig.missingNumber, RPRef.missingNumber, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.missingNumber RPRef.missingNumber; rfl))
    | (simp only [RPOrig.missingNumber, RPRef.missingNumber, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.missingNumber RPRef.missingNumber; rfl))
    | (simp only [RPOrig.missingNumber, RPRef.missingNumber]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.missingNumber RPRef.missingNumber; rfl))

theorem rp_equiv_simp (nums : List Nat) (h_precond : missingNumber_precond (nums)) :
    RPOrig.missingNumber nums h_precond = RPRef.missingNumber nums h_precond := by
  first
    | (simp [RPOrig.missingNumber, RPRef.missingNumber, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.missingNumber RPRef.missingNumber; rfl))
    | (simp [RPOrig.missingNumber, RPRef.missingNumber, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.missingNumber RPRef.missingNumber; rfl))
    | (simp [RPOrig.missingNumber, RPRef.missingNumber, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.missingNumber RPRef.missingNumber; rfl))
    | (simp [RPOrig.missingNumber, RPRef.missingNumber]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.missingNumber RPRef.missingNumber; rfl))

theorem rp_equiv_ac_rfl (nums : List Nat) (h_precond : missingNumber_precond (nums)) :
    RPOrig.missingNumber nums h_precond = RPRef.missingNumber nums h_precond := by
  (try simp only [RPOrig.missingNumber, RPRef.missingNumber]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.missingNumber RPRef.missingNumber; rfl))
