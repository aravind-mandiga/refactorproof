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
private def longestIncreasingStreak__rp_helper_1de4754d (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) : Nat :=
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

def longestIncreasingStreak (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) : Nat :=
  longestIncreasingStreak__rp_helper_1de4754d nums h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) :
    RPOrig.longestIncreasingStreak nums h_precond = RPRef.longestIncreasingStreak nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) :
    RPOrig.longestIncreasingStreak nums h_precond = RPRef.longestIncreasingStreak nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) :
    RPOrig.longestIncreasingStreak nums h_precond = RPRef.longestIncreasingStreak nums h_precond := by
  delta RPOrig.longestIncreasingStreak RPRef.longestIncreasingStreak RPRef.longestIncreasingStreak__rp_helper_1de4754d RPOrig.longestIncreasingStreak.aux RPRef.longestIncreasingStreak__rp_helper_1de4754d.aux
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) :
    RPOrig.longestIncreasingStreak nums h_precond = RPRef.longestIncreasingStreak nums h_precond := by
  (simp only [RPOrig.longestIncreasingStreak, RPRef.longestIncreasingStreak, RPRef.longestIncreasingStreak__rp_helper_1de4754d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingStreak RPRef.longestIncreasingStreak RPRef.longestIncreasingStreak__rp_helper_1de4754d RPOrig.longestIncreasingStreak.aux RPRef.longestIncreasingStreak__rp_helper_1de4754d.aux; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : longestIncreasingStreak_precond (nums)) :
    RPOrig.longestIncreasingStreak nums h_precond = RPRef.longestIncreasingStreak nums h_precond := by
  (simp [RPOrig.longestIncreasingStreak, RPRef.longestIncreasingStreak, RPRef.longestIncreasingStreak__rp_helper_1de4754d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingStreak RPRef.longestIncreasingStreak RPRef.longestIncreasingStreak__rp_helper_1de4754d RPOrig.longestIncreasingStreak.aux RPRef.longestIncreasingStreak__rp_helper_1de4754d.aux; rfl))
