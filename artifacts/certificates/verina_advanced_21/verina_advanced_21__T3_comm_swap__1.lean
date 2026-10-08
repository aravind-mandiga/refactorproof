-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def isPalindrome_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def isPalindrome (s : String) (h_precond : isPalindrome_precond (s)) : Bool :=
  let length := s.length

if length <= 1 then
  true
else
  let arr := s.toList

  let rec checkIndices (left : Nat) (right : Nat) (chars : List Char) : Bool :=
    if left >= right then
      true
    else
      match chars[left]?, chars[right]? with
      | some cLeft, some cRight =>
        if cLeft == cRight then
          checkIndices (left + 1) (right - 1) chars
        else
          false
      | _, _ => false
  let approach1 := checkIndices 0 (length - 1) arr

  let rec reverseList (acc : List Char) (xs : List Char) : List Char :=
    match xs with
    | []      => acc
    | h :: t  => reverseList (h :: acc) t
  let reversed := reverseList [] arr
  let approach2 := (arr == reversed)

  approach1 && approach2
end RPOrig

namespace RPRef

def isPalindrome (s : String) (h_precond : isPalindrome_precond (s)) : Bool :=
  let length := s.length

if length <= 1 then
  true
else
  let arr := s.toList

  let rec checkIndices (left : Nat) (right : Nat) (chars : List Char) : Bool :=
    if left >= right then
      true
    else
      match chars[left]?, chars[right]? with
      | some cLeft, some cRight =>
        if cLeft == cRight then
          checkIndices (left + 1) (right - 1) chars
        else
          false
      | _, _ => false
  let approach1 := checkIndices 0 (length - 1) arr

  let rec reverseList (acc : List Char) (xs : List Char) : List Char :=
    match xs with
    | []      => acc
    | h :: t  => reverseList (h :: acc) t
  let reversed := reverseList [] arr
  let approach2 := (arr == reversed)

  approach2 && approach1
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := by
  delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := by
  first
    | (simp only [RPOrig.isPalindrome, RPRef.isPalindrome, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))
    | (simp only [RPOrig.isPalindrome, RPRef.isPalindrome, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))
    | (simp only [RPOrig.isPalindrome, RPRef.isPalindrome, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))
    | (simp only [RPOrig.isPalindrome, RPRef.isPalindrome]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))

theorem rp_equiv_simp (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := by
  first
    | (simp [RPOrig.isPalindrome, RPRef.isPalindrome, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))
    | (simp [RPOrig.isPalindrome, RPRef.isPalindrome, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))
    | (simp [RPOrig.isPalindrome, RPRef.isPalindrome, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))
    | (simp [RPOrig.isPalindrome, RPRef.isPalindrome]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))

theorem rp_equiv_ac_rfl (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := by
  (try simp only [RPOrig.isPalindrome, RPRef.isPalindrome]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))
