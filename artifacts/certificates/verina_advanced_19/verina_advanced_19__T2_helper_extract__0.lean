-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
-- Check if a character is an uppercase alphabet letter
def isUpperAlpha (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

-- Check if a character is a lowercase alphabet letter
def isLowerAlpha (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

-- Determine if a character is alphabetic
def isAlpha (c : Char) : Bool :=
  isUpperAlpha c ∨ isLowerAlpha c

-- Convert a single character to lowercase
def toLower (c : Char) : Char :=
  if isUpperAlpha c then Char.ofNat (c.toNat + 32) else c

-- Normalize a character: keep only lowercase letters
def normalizeChar (c : Char) : Option Char :=
  if isAlpha c then some (toLower c) else none

-- Normalize a string into a list of lowercase alphabetic characters
def normalizeString (s : String) : List Char :=
  s.toList.foldr (fun c acc =>
    match normalizeChar c with
    | some c' => c' :: acc
    | none    => acc
  ) []
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def isCleanPalindrome_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
-- Reverse the list
def reverseList (xs : List Char) : List Char :=
  xs.reverse

namespace RPOrig

def isCleanPalindrome (s : String) (h_precond : isCleanPalindrome_precond (s)) : Bool :=
  let norm := normalizeString s
  norm = reverseList norm
end RPOrig

namespace RPRef

private def isCleanPalindrome__rp_helper_041e7c9a (s : String) (h_precond : isCleanPalindrome_precond (s)) : Bool :=
  let norm := normalizeString s
  norm = reverseList norm

def isCleanPalindrome (s : String) (h_precond : isCleanPalindrome_precond (s)) : Bool :=
  isCleanPalindrome__rp_helper_041e7c9a s h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : isCleanPalindrome_precond (s)) :
    RPOrig.isCleanPalindrome s h_precond = RPRef.isCleanPalindrome s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : isCleanPalindrome_precond (s)) :
    RPOrig.isCleanPalindrome s h_precond = RPRef.isCleanPalindrome s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : isCleanPalindrome_precond (s)) :
    RPOrig.isCleanPalindrome s h_precond = RPRef.isCleanPalindrome s h_precond := by
  delta RPOrig.isCleanPalindrome RPRef.isCleanPalindrome RPRef.isCleanPalindrome__rp_helper_041e7c9a
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : isCleanPalindrome_precond (s)) :
    RPOrig.isCleanPalindrome s h_precond = RPRef.isCleanPalindrome s h_precond := by
  (simp only [RPOrig.isCleanPalindrome, RPRef.isCleanPalindrome, RPRef.isCleanPalindrome__rp_helper_041e7c9a]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isCleanPalindrome RPRef.isCleanPalindrome RPRef.isCleanPalindrome__rp_helper_041e7c9a; rfl))

theorem rp_equiv_simp (s : String) (h_precond : isCleanPalindrome_precond (s)) :
    RPOrig.isCleanPalindrome s h_precond = RPRef.isCleanPalindrome s h_precond := by
  (simp [RPOrig.isCleanPalindrome, RPRef.isCleanPalindrome, RPRef.isCleanPalindrome__rp_helper_041e7c9a]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isCleanPalindrome RPRef.isCleanPalindrome RPRef.isCleanPalindrome__rp_helper_041e7c9a; rfl))
