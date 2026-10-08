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

if ¬ (length <= 1) then
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
else
  true
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
    | (simp only [RPOrig.isPalindrome, RPRef.isPalindrome, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))
    | (simp only [RPOrig.isPalindrome, RPRef.isPalindrome, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))
    | (simp only [RPOrig.isPalindrome, RPRef.isPalindrome]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))

theorem rp_equiv_simp (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := by
  first
    | (simp [RPOrig.isPalindrome, RPRef.isPalindrome, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))
    | (simp [RPOrig.isPalindrome, RPRef.isPalindrome, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))
    | (simp [RPOrig.isPalindrome, RPRef.isPalindrome]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))

theorem rp_equiv_bycases (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := by
  by_cases h : (length <= 1) <;> (try simp [h, RPOrig.isPalindrome, RPRef.isPalindrome]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))

theorem rp_equiv_bycases_ite (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := by
  by_cases h : (length <= 1) <;> (try simp [h, ite_not, RPOrig.isPalindrome, RPRef.isPalindrome]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))

theorem rp_equiv_split_simp_all (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := by
  simp only [RPOrig.isPalindrome, RPRef.isPalindrome]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome.checkIndices RPRef.isPalindrome.reverseList; rfl))
