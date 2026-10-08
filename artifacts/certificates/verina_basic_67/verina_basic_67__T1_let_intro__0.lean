-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def IsPalindrome_precond (x : List Char) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def isPalindromeHelper (x : List Char) (i j : Nat) : Bool :=
  if i < j then
    match x[i]?, x[j]? with
    | some ci, some cj =>
      if ci ≠ cj then false else isPalindromeHelper x (i + 1) (j - 1)
    | _, _ => false  -- This case should not occur due to valid indices
  else true

namespace RPOrig

def IsPalindrome (x : List Char) (h_precond : IsPalindrome_precond (x)) : Bool :=
  if x.length = 0 then true else isPalindromeHelper x 0 (x.length - 1)
end RPOrig

namespace RPRef

def IsPalindrome (x : List Char) (h_precond : IsPalindrome_precond (x)) : Bool :=
  let __rp_tmp_11947550 : Bool :=
    if x.length = 0 then true else isPalindromeHelper x 0 (x.length - 1)
  __rp_tmp_11947550
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (x : List Char) (h_precond : IsPalindrome_precond (x)) :
    RPOrig.IsPalindrome x h_precond = RPRef.IsPalindrome x h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (x : List Char) (h_precond : IsPalindrome_precond (x)) :
    RPOrig.IsPalindrome x h_precond = RPRef.IsPalindrome x h_precond := rfl

theorem rp_equiv_delta_rfl (x : List Char) (h_precond : IsPalindrome_precond (x)) :
    RPOrig.IsPalindrome x h_precond = RPRef.IsPalindrome x h_precond := by
  delta RPOrig.IsPalindrome RPRef.IsPalindrome
  rfl

theorem rp_equiv_simp_only (x : List Char) (h_precond : IsPalindrome_precond (x)) :
    RPOrig.IsPalindrome x h_precond = RPRef.IsPalindrome x h_precond := by
  (simp only [RPOrig.IsPalindrome, RPRef.IsPalindrome]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.IsPalindrome RPRef.IsPalindrome; rfl))

theorem rp_equiv_simp (x : List Char) (h_precond : IsPalindrome_precond (x)) :
    RPOrig.IsPalindrome x h_precond = RPRef.IsPalindrome x h_precond := by
  (simp [RPOrig.IsPalindrome, RPRef.IsPalindrome]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.IsPalindrome RPRef.IsPalindrome; rfl))
