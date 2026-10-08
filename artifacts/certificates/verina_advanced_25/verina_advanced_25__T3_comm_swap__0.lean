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

def lengthOfLIS (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) : Nat :=
  if nums.isEmpty then 0
  else
    let n := nums.length
    Id.run do
      let mut dp : Array Nat := Array.mkArray n 1

      for i in [1:n] do
        for j in [0:i] do
          if nums[j]! < nums[i]! && dp[j]! + 1 > dp[i]! then
            dp := dp.set! i (1 + dp[j]!)

      maxInArray dp
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := by
  delta RPOrig.lengthOfLIS RPRef.lengthOfLIS
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := by
  first
    | (simp only [RPOrig.lengthOfLIS, RPRef.lengthOfLIS, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lengthOfLIS RPRef.lengthOfLIS; rfl))
    | (simp only [RPOrig.lengthOfLIS, RPRef.lengthOfLIS, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lengthOfLIS RPRef.lengthOfLIS; rfl))
    | (simp only [RPOrig.lengthOfLIS, RPRef.lengthOfLIS, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lengthOfLIS RPRef.lengthOfLIS; rfl))
    | (simp only [RPOrig.lengthOfLIS, RPRef.lengthOfLIS]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lengthOfLIS RPRef.lengthOfLIS; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := by
  first
    | (simp [RPOrig.lengthOfLIS, RPRef.lengthOfLIS, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lengthOfLIS RPRef.lengthOfLIS; rfl))
    | (simp [RPOrig.lengthOfLIS, RPRef.lengthOfLIS, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lengthOfLIS RPRef.lengthOfLIS; rfl))
    | (simp [RPOrig.lengthOfLIS, RPRef.lengthOfLIS, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lengthOfLIS RPRef.lengthOfLIS; rfl))
    | (simp [RPOrig.lengthOfLIS, RPRef.lengthOfLIS]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lengthOfLIS RPRef.lengthOfLIS; rfl))

theorem rp_equiv_ac_rfl (nums : List Int) (h_precond : lengthOfLIS_precond (nums)) :
    RPOrig.lengthOfLIS nums h_precond = RPRef.lengthOfLIS nums h_precond := by
  (try simp only [RPOrig.lengthOfLIS, RPRef.lengthOfLIS]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lengthOfLIS RPRef.lengthOfLIS; rfl))
