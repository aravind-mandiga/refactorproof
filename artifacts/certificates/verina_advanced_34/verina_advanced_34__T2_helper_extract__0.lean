-- !benchmark @start import type=solution
import Mathlib.Data.List.Basic
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def binarySearchLeft (sub : Array Int) (num : Int) (left right : Nat) : Nat :=
  if h : left < right then
    let mid := (left + right) / 2
    if sub[mid]! == num then
      binarySearchLeft sub num left mid
    else if sub[mid]! < num then
      binarySearchLeft sub num (mid + 1) right
    else
      binarySearchLeft sub num left mid
  else
    left
termination_by right - left

namespace RPOrig

def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Int :=
  Id.run do
    if nums.isEmpty then return 0
    let mut sub : Array Int := Array.empty
    sub := sub.push nums.head!
    for num in nums.tail do
      if num > sub[sub.size - 1]! then
        sub := sub.push num
      else
        let left := binarySearchLeft sub num 0 (sub.size - 1)
        sub := sub.set! left num
    return Int.ofNat sub.size
end RPOrig

namespace RPRef

private def longestIncreasingSubsequence__rp_helper_325e1b4a (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Int :=
  Id.run do
    if nums.isEmpty then return 0
    let mut sub : Array Int := Array.empty
    sub := sub.push nums.head!
    for num in nums.tail do
      if num > sub[sub.size - 1]! then
        sub := sub.push num
      else
        let left := binarySearchLeft sub num 0 (sub.size - 1)
        sub := sub.set! left num
    return Int.ofNat sub.size

def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Int :=
  longestIncreasingSubsequence__rp_helper_325e1b4a nums h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    RPOrig.longestIncreasingSubsequence nums h_precond = RPRef.longestIncreasingSubsequence nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    RPOrig.longestIncreasingSubsequence nums h_precond = RPRef.longestIncreasingSubsequence nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    RPOrig.longestIncreasingSubsequence nums h_precond = RPRef.longestIncreasingSubsequence nums h_precond := by
  delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence__rp_helper_325e1b4a
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    RPOrig.longestIncreasingSubsequence nums h_precond = RPRef.longestIncreasingSubsequence nums h_precond := by
  (simp only [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence__rp_helper_325e1b4a]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence__rp_helper_325e1b4a; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    RPOrig.longestIncreasingSubsequence nums h_precond = RPRef.longestIncreasingSubsequence nums h_precond := by
  (simp [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence__rp_helper_325e1b4a]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence__rp_helper_325e1b4a; rfl))
