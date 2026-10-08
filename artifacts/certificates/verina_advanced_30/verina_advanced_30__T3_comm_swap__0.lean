-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def longestIncreasingStreak_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def longestIncreasingStreak (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) : Nat :=
  let rec aux (lst : List Int) (prev : Option Int) (currLen : Nat) (maxLen : Nat) : Nat :=
    match lst with
    | [] => max currLen maxLen
    | x :: xs =>
      match prev with
      | none => aux xs (some x) 1 (max 1 maxLen)
      | some p =>
        if x > p then aux xs (some x) (currLen + 1) (max (currLen + 1) maxLen)
        else aux xs (some x) 1 (max currLen maxLen)
  aux nums none 0 0
end RPOrig

namespace RPRef

def longestIncreasingStreak (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) : Nat :=
  let rec aux (lst : List Int) (prev : Option Int) (currLen : Nat) (maxLen : Nat) : Nat :=
    match lst with
    | [] => max currLen maxLen
    | x :: xs =>
      match prev with
      | none => aux xs (some x) 1 (max 1 maxLen)
      | some p =>
        if x > p then aux xs (some x) (1 + currLen) (max (currLen + 1) maxLen)
        else aux xs (some x) 1 (max currLen maxLen)
  aux nums none 0 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) :
    RPOrig.longestIncreasingStreak nums h_precond = RPRef.longestIncreasingStreak nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) :
    RPOrig.longestIncreasingStreak nums h_precond = RPRef.longestIncreasingStreak nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) :
    RPOrig.longestIncreasingStreak nums h_precond = RPRef.longestIncreasingStreak nums h_precond := by
  delta RPOrig.longestIncreasingStreak RPRef.longestIncreasingStreak RPOrig.longestIncreasingStreak.aux RPRef.longestIncreasingStreak.aux
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) :
    RPOrig.longestIncreasingStreak nums h_precond = RPRef.longestIncreasingStreak nums h_precond := by
  first
    | (simp only [RPOrig.longestIncreasingStreak, RPRef.longestIncreasingStreak, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingStreak RPRef.longestIncreasingStreak RPOrig.longestIncreasingStreak.aux RPRef.longestIncreasingStreak.aux; rfl))
    | (simp only [RPOrig.longestIncreasingStreak, RPRef.longestIncreasingStreak, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingStreak RPRef.longestIncreasingStreak RPOrig.longestIncreasingStreak.aux RPRef.longestIncreasingStreak.aux; rfl))
    | (simp only [RPOrig.longestIncreasingStreak, RPRef.longestIncreasingStreak, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingStreak RPRef.longestIncreasingStreak RPOrig.longestIncreasingStreak.aux RPRef.longestIncreasingStreak.aux; rfl))
    | (simp only [RPOrig.longestIncreasingStreak, RPRef.longestIncreasingStreak]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingStreak RPRef.longestIncreasingStreak RPOrig.longestIncreasingStreak.aux RPRef.longestIncreasingStreak.aux; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) :
    RPOrig.longestIncreasingStreak nums h_precond = RPRef.longestIncreasingStreak nums h_precond := by
  first
    | (simp [RPOrig.longestIncreasingStreak, RPRef.longestIncreasingStreak, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingStreak RPRef.longestIncreasingStreak RPOrig.longestIncreasingStreak.aux RPRef.longestIncreasingStreak.aux; rfl))
    | (simp [RPOrig.longestIncreasingStreak, RPRef.longestIncreasingStreak, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingStreak RPRef.longestIncreasingStreak RPOrig.longestIncreasingStreak.aux RPRef.longestIncreasingStreak.aux; rfl))
    | (simp [RPOrig.longestIncreasingStreak, RPRef.longestIncreasingStreak, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingStreak RPRef.longestIncreasingStreak RPOrig.longestIncreasingStreak.aux RPRef.longestIncreasingStreak.aux; rfl))
    | (simp [RPOrig.longestIncreasingStreak, RPRef.longestIncreasingStreak]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingStreak RPRef.longestIncreasingStreak RPOrig.longestIncreasingStreak.aux RPRef.longestIncreasingStreak.aux; rfl))

theorem rp_equiv_ac_rfl (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) :
    RPOrig.longestIncreasingStreak nums h_precond = RPRef.longestIncreasingStreak nums h_precond := by
  (try simp only [RPOrig.longestIncreasingStreak, RPRef.longestIncreasingStreak]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingStreak RPRef.longestIncreasingStreak RPOrig.longestIncreasingStreak.aux RPRef.longestIncreasingStreak.aux; rfl))
