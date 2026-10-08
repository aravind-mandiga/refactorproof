-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LongestCommonPrefix_precond (str1 : List Char) (str2 : List Char) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def LongestCommonPrefix (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) : List Char :=
  let minLength := Nat.min str1.length str2.length
  let rec aux (idx : Nat) (acc : List Char) : List Char :=
    if idx < minLength then
      match str1[idx]?, str2[idx]? with
      | some c1, some c2 =>
          if c1 ≠ c2 then acc
          else aux (idx + 1) (acc ++ [c1])
      | _, _ => acc
    else acc
  aux 0 []
end RPOrig

namespace RPRef

def LongestCommonPrefix (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) : List Char :=
  let minLength := Nat.min str1.length str2.length
  let rec aux (idx : Nat) (acc : List Char) : List Char :=
    if idx < minLength then
      match str1[idx]?, str2[idx]? with
      | some c1, some c2 =>
          if c1 ≠ c2 then acc
          else aux (1 + idx) (acc ++ [c1])
      | _, _ => acc
    else acc
  aux 0 []
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    RPOrig.LongestCommonPrefix str1 str2 h_precond = RPRef.LongestCommonPrefix str1 str2 h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    RPOrig.LongestCommonPrefix str1 str2 h_precond = RPRef.LongestCommonPrefix str1 str2 h_precond := rfl

theorem rp_equiv_delta_rfl (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    RPOrig.LongestCommonPrefix str1 str2 h_precond = RPRef.LongestCommonPrefix str1 str2 h_precond := by
  delta RPOrig.LongestCommonPrefix RPRef.LongestCommonPrefix RPOrig.LongestCommonPrefix.aux RPRef.LongestCommonPrefix.aux
  rfl

theorem rp_equiv_simp_only (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    RPOrig.LongestCommonPrefix str1 str2 h_precond = RPRef.LongestCommonPrefix str1 str2 h_precond := by
  first
    | (simp only [RPOrig.LongestCommonPrefix, RPRef.LongestCommonPrefix, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonPrefix RPRef.LongestCommonPrefix RPOrig.LongestCommonPrefix.aux RPRef.LongestCommonPrefix.aux; rfl))
    | (simp only [RPOrig.LongestCommonPrefix, RPRef.LongestCommonPrefix, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonPrefix RPRef.LongestCommonPrefix RPOrig.LongestCommonPrefix.aux RPRef.LongestCommonPrefix.aux; rfl))
    | (simp only [RPOrig.LongestCommonPrefix, RPRef.LongestCommonPrefix, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonPrefix RPRef.LongestCommonPrefix RPOrig.LongestCommonPrefix.aux RPRef.LongestCommonPrefix.aux; rfl))
    | (simp only [RPOrig.LongestCommonPrefix, RPRef.LongestCommonPrefix]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonPrefix RPRef.LongestCommonPrefix RPOrig.LongestCommonPrefix.aux RPRef.LongestCommonPrefix.aux; rfl))

theorem rp_equiv_simp (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    RPOrig.LongestCommonPrefix str1 str2 h_precond = RPRef.LongestCommonPrefix str1 str2 h_precond := by
  first
    | (simp [RPOrig.LongestCommonPrefix, RPRef.LongestCommonPrefix, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonPrefix RPRef.LongestCommonPrefix RPOrig.LongestCommonPrefix.aux RPRef.LongestCommonPrefix.aux; rfl))
    | (simp [RPOrig.LongestCommonPrefix, RPRef.LongestCommonPrefix, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonPrefix RPRef.LongestCommonPrefix RPOrig.LongestCommonPrefix.aux RPRef.LongestCommonPrefix.aux; rfl))
    | (simp [RPOrig.LongestCommonPrefix, RPRef.LongestCommonPrefix, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonPrefix RPRef.LongestCommonPrefix RPOrig.LongestCommonPrefix.aux RPRef.LongestCommonPrefix.aux; rfl))
    | (simp [RPOrig.LongestCommonPrefix, RPRef.LongestCommonPrefix]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonPrefix RPRef.LongestCommonPrefix RPOrig.LongestCommonPrefix.aux RPRef.LongestCommonPrefix.aux; rfl))

theorem rp_equiv_ac_rfl (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    RPOrig.LongestCommonPrefix str1 str2 h_precond = RPRef.LongestCommonPrefix str1 str2 h_precond := by
  (try simp only [RPOrig.LongestCommonPrefix, RPRef.LongestCommonPrefix]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonPrefix RPRef.LongestCommonPrefix RPOrig.LongestCommonPrefix.aux RPRef.LongestCommonPrefix.aux; rfl))
