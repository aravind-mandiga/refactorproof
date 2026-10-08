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
private def LongestCommonPrefix__rp_helper_cb9daf18 (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) : List Char :=
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

def LongestCommonPrefix (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) : List Char :=
  LongestCommonPrefix__rp_helper_cb9daf18 str1 str2 h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    RPOrig.LongestCommonPrefix str1 str2 h_precond = RPRef.LongestCommonPrefix str1 str2 h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    RPOrig.LongestCommonPrefix str1 str2 h_precond = RPRef.LongestCommonPrefix str1 str2 h_precond := rfl

theorem rp_equiv_delta_rfl (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    RPOrig.LongestCommonPrefix str1 str2 h_precond = RPRef.LongestCommonPrefix str1 str2 h_precond := by
  delta RPOrig.LongestCommonPrefix RPRef.LongestCommonPrefix RPRef.LongestCommonPrefix__rp_helper_cb9daf18 RPOrig.LongestCommonPrefix.aux RPRef.LongestCommonPrefix__rp_helper_cb9daf18.aux
  rfl

theorem rp_equiv_simp_only (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    RPOrig.LongestCommonPrefix str1 str2 h_precond = RPRef.LongestCommonPrefix str1 str2 h_precond := by
  (simp only [RPOrig.LongestCommonPrefix, RPRef.LongestCommonPrefix, RPRef.LongestCommonPrefix__rp_helper_cb9daf18]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonPrefix RPRef.LongestCommonPrefix RPRef.LongestCommonPrefix__rp_helper_cb9daf18 RPOrig.LongestCommonPrefix.aux RPRef.LongestCommonPrefix__rp_helper_cb9daf18.aux; rfl))

theorem rp_equiv_simp (str1 : List Char) (str2 : List Char) (h_precond : LongestCommonPrefix_precond (str1) (str2)) :
    RPOrig.LongestCommonPrefix str1 str2 h_precond = RPRef.LongestCommonPrefix str1 str2 h_precond := by
  (simp [RPOrig.LongestCommonPrefix, RPRef.LongestCommonPrefix, RPRef.LongestCommonPrefix__rp_helper_cb9daf18]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LongestCommonPrefix RPRef.LongestCommonPrefix RPRef.LongestCommonPrefix__rp_helper_cb9daf18 RPOrig.LongestCommonPrefix.aux RPRef.LongestCommonPrefix__rp_helper_cb9daf18.aux; rfl))
