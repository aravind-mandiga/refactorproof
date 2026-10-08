-- !benchmark @start import type=solution
import Std.Data.HashMap
-- !benchmark @end import

-- !benchmark @start solution_aux
open Std
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def longestGoodSubarray_precond (nums : List Nat) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k > 0  -- k must be positive for non-trivial subarrays
  -- !benchmark @end precond



namespace RPOrig

def longestGoodSubarray (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) : Nat :=
  Id.run do
    let arr := nums.toArray
    let mut left := 0
    let mut maxLen := 0
    let mut freq : HashMap Nat Nat := {}

    for right in [0:arr.size] do
      let num := arr[right]!
      let count := freq.getD num 0
      freq := freq.insert num (count + 1)

      for _ in List.range arr.size do
        if freq.toList.any (fun (_, v) => v > k) then
          let lnum := arr[left]!
          let lcount := freq.getD lnum 0
          if lcount = 1 then
            freq := freq.erase lnum
          else
            freq := freq.insert lnum (lcount - 1)
          left := left + 1
        else
          break

      maxLen := max maxLen (right - left + 1)

    return maxLen
end RPOrig

namespace RPRef
private def longestGoodSubarray__rp_helper_6bcfd864 (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) : Nat :=
  Id.run do
    let arr := nums.toArray
    let mut left := 0
    let mut maxLen := 0
    let mut freq : HashMap Nat Nat := {}

    for right in [0:arr.size] do
      let num := arr[right]!
      let count := freq.getD num 0
      freq := freq.insert num (count + 1)

      for _ in List.range arr.size do
        if freq.toList.any (fun (_, v) => v > k) then
          let lnum := arr[left]!
          let lcount := freq.getD lnum 0
          if lcount = 1 then
            freq := freq.erase lnum
          else
            freq := freq.insert lnum (lcount - 1)
          left := left + 1
        else
          break

      maxLen := max maxLen (right - left + 1)

    return maxLen

def longestGoodSubarray (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) : Nat :=
  longestGoodSubarray__rp_helper_6bcfd864 nums k h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) :
    RPOrig.longestGoodSubarray nums k h_precond = RPRef.longestGoodSubarray nums k h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) :
    RPOrig.longestGoodSubarray nums k h_precond = RPRef.longestGoodSubarray nums k h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) :
    RPOrig.longestGoodSubarray nums k h_precond = RPRef.longestGoodSubarray nums k h_precond := by
  delta RPOrig.longestGoodSubarray RPRef.longestGoodSubarray RPRef.longestGoodSubarray__rp_helper_6bcfd864
  rfl

theorem rp_equiv_simp_only (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) :
    RPOrig.longestGoodSubarray nums k h_precond = RPRef.longestGoodSubarray nums k h_precond := by
  (simp only [RPOrig.longestGoodSubarray, RPRef.longestGoodSubarray, RPRef.longestGoodSubarray__rp_helper_6bcfd864]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestGoodSubarray RPRef.longestGoodSubarray RPRef.longestGoodSubarray__rp_helper_6bcfd864; rfl))

theorem rp_equiv_simp (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) :
    RPOrig.longestGoodSubarray nums k h_precond = RPRef.longestGoodSubarray nums k h_precond := by
  (simp [RPOrig.longestGoodSubarray, RPRef.longestGoodSubarray, RPRef.longestGoodSubarray__rp_helper_6bcfd864]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestGoodSubarray RPRef.longestGoodSubarray RPRef.longestGoodSubarray__rp_helper_6bcfd864; rfl))
