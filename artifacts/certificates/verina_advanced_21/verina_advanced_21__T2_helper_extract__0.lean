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
private def isPalindrome__rp_helper_89ce9017 (s : String) (h_precond : isPalindrome_precond (s)) : Bool :=
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

def isPalindrome (s : String) (h_precond : isPalindrome_precond (s)) : Bool :=
isPalindrome__rp_helper_89ce9017 s h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := by
  delta RPOrig.isPalindrome RPRef.isPalindrome RPRef.isPalindrome__rp_helper_89ce9017 RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome__rp_helper_89ce9017.checkIndices RPRef.isPalindrome__rp_helper_89ce9017.reverseList
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := by
  (simp only [RPOrig.isPalindrome, RPRef.isPalindrome, RPRef.isPalindrome__rp_helper_89ce9017]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPRef.isPalindrome__rp_helper_89ce9017 RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome__rp_helper_89ce9017.checkIndices RPRef.isPalindrome__rp_helper_89ce9017.reverseList; rfl))

theorem rp_equiv_simp (s : String) (h_precond : isPalindrome_precond (s)) :
    RPOrig.isPalindrome s h_precond = RPRef.isPalindrome s h_precond := by
  (simp [RPOrig.isPalindrome, RPRef.isPalindrome, RPRef.isPalindrome__rp_helper_89ce9017]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPalindrome RPRef.isPalindrome RPRef.isPalindrome__rp_helper_89ce9017 RPOrig.isPalindrome.checkIndices RPOrig.isPalindrome.reverseList RPRef.isPalindrome__rp_helper_89ce9017.checkIndices RPRef.isPalindrome__rp_helper_89ce9017.reverseList; rfl))
