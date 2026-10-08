-- !benchmark @start import type=solution
import Mathlib.Data.List.Basic
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def lengthOfLIS_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def maxInArray (arr : Array Nat) : Nat :=
  arr.foldl (fun a b => if a ≥ b then a else b) 0

namespace RPOrig

def lengthOfLIS (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Nat :=
  if nums.isEmpty then 0
  else
    let n := nums.length
    Id.run do
      let mut dp : Array Nat := Array.mkArray n 1

      for i in [1:n] do
        for j in [0:i] do
          if nums[j]! < nums[i]! && dp[j]! + 1 > dp[i]! then
            dp := dp.set! i (dp[j]! + 1)

      maxInArray dp
end RPOrig

namespace RPRef

private def lengthOfLIS__rp_helper_c53bb958 (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Nat :=
  if nums.isEmpty then 0
  else
    let n := nums.length
    Id.run do
      let mut dp : Array Nat := Array.mkArray n 1

      for i in [1:n] do
        for j in [0:i] do
          if nums[j]! < nums[i]! && dp[j]! + 1 > dp[i]! then
            dp := dp.set! i (dp[j]! + 1)

      maxInArray dp

def lengthOfLIS (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Nat :=
  lengthOfLIS__rp_helper_c53bb958 nums h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := by
  delta RPOrig.lengthOfLIS RPRef.lengthOfLIS RPRef.lengthOfLIS__rp_helper_c53bb958
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := by
  (simp only [RPOrig.lengthOfLIS, RPRef.lengthOfLIS, RPRef.lengthOfLIS__rp_helper_c53bb958]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lengthOfLIS RPRef.lengthOfLIS RPRef.lengthOfLIS__rp_helper_c53bb958; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := by
  (simp [RPOrig.lengthOfLIS, RPRef.lengthOfLIS, RPRef.lengthOfLIS__rp_helper_c53bb958]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lengthOfLIS RPRef.lengthOfLIS RPRef.lengthOfLIS__rp_helper_c53bb958; rfl))
