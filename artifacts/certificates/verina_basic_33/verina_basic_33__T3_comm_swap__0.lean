-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def smallestMissingNumber_precond (s : List Nat) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) s
  -- !benchmark @end precond


namespace RPOrig

def smallestMissingNumber (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) : Nat :=
  let rec findMissing (v : Nat) (l : List Nat) : Nat :=
    match l with
    | [] => v
    | x :: xs =>
      if x > v then v
      else if x = v then findMissing (v + 1) xs
      else findMissing v xs
  findMissing 0 s
end RPOrig

namespace RPRef

def smallestMissingNumber (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) : Nat :=
  let rec findMissing (v : Nat) (l : List Nat) : Nat :=
    match l with
    | [] => v
    | x :: xs =>
      if x > v then v
      else if x = v then findMissing (1 + v) xs
      else findMissing v xs
  findMissing 0 s
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    RPOrig.smallestMissingNumber s h_precond = RPRef.smallestMissingNumber s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    RPOrig.smallestMissingNumber s h_precond = RPRef.smallestMissingNumber s h_precond := rfl

theorem rp_equiv_delta_rfl (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    RPOrig.smallestMissingNumber s h_precond = RPRef.smallestMissingNumber s h_precond := by
  delta RPOrig.smallestMissingNumber RPRef.smallestMissingNumber RPOrig.smallestMissingNumber.findMissing RPRef.smallestMissingNumber.findMissing
  rfl

theorem rp_equiv_simp_only (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    RPOrig.smallestMissingNumber s h_precond = RPRef.smallestMissingNumber s h_precond := by
  first
    | (simp only [RPOrig.smallestMissingNumber, RPRef.smallestMissingNumber, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissingNumber RPRef.smallestMissingNumber RPOrig.smallestMissingNumber.findMissing RPRef.smallestMissingNumber.findMissing; rfl))
    | (simp only [RPOrig.smallestMissingNumber, RPRef.smallestMissingNumber, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissingNumber RPRef.smallestMissingNumber RPOrig.smallestMissingNumber.findMissing RPRef.smallestMissingNumber.findMissing; rfl))
    | (simp only [RPOrig.smallestMissingNumber, RPRef.smallestMissingNumber, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissingNumber RPRef.smallestMissingNumber RPOrig.smallestMissingNumber.findMissing RPRef.smallestMissingNumber.findMissing; rfl))
    | (simp only [RPOrig.smallestMissingNumber, RPRef.smallestMissingNumber]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissingNumber RPRef.smallestMissingNumber RPOrig.smallestMissingNumber.findMissing RPRef.smallestMissingNumber.findMissing; rfl))

theorem rp_equiv_simp (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    RPOrig.smallestMissingNumber s h_precond = RPRef.smallestMissingNumber s h_precond := by
  first
    | (simp [RPOrig.smallestMissingNumber, RPRef.smallestMissingNumber, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissingNumber RPRef.smallestMissingNumber RPOrig.smallestMissingNumber.findMissing RPRef.smallestMissingNumber.findMissing; rfl))
    | (simp [RPOrig.smallestMissingNumber, RPRef.smallestMissingNumber, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissingNumber RPRef.smallestMissingNumber RPOrig.smallestMissingNumber.findMissing RPRef.smallestMissingNumber.findMissing; rfl))
    | (simp [RPOrig.smallestMissingNumber, RPRef.smallestMissingNumber, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissingNumber RPRef.smallestMissingNumber RPOrig.smallestMissingNumber.findMissing RPRef.smallestMissingNumber.findMissing; rfl))
    | (simp [RPOrig.smallestMissingNumber, RPRef.smallestMissingNumber]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissingNumber RPRef.smallestMissingNumber RPOrig.smallestMissingNumber.findMissing RPRef.smallestMissingNumber.findMissing; rfl))

theorem rp_equiv_ac_rfl (s : List Nat) (h_precond : smallestMissingNumber_precond (s)) :
    RPOrig.smallestMissingNumber s h_precond = RPRef.smallestMissingNumber s h_precond := by
  (try simp only [RPOrig.smallestMissingNumber, RPRef.smallestMissingNumber]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissingNumber RPRef.smallestMissingNumber RPOrig.smallestMissingNumber.findMissing RPRef.smallestMissingNumber.findMissing; rfl))
