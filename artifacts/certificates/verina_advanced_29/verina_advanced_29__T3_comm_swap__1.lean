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
          left := 1 + left
        else
          break

      maxLen := max maxLen (right - left + 1)

    return maxLen
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) :
    RPOrig.longestGoodSubarray nums k h_precond = RPRef.longestGoodSubarray nums k h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) :
    RPOrig.longestGoodSubarray nums k h_precond = RPRef.longestGoodSubarray nums k h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) :
    RPOrig.longestGoodSubarray nums k h_precond = RPRef.longestGoodSubarray nums k h_precond := by
  delta RPOrig.longestGoodSubarray RPRef.longestGoodSubarray
  rfl

theorem rp_equiv_simp_only (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) :
    RPOrig.longestGoodSubarray nums k h_precond = RPRef.longestGoodSubarray nums k h_precond := by
  first
    | (simp only [RPOrig.longestGoodSubarray, RPRef.longestGoodSubarray, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestGoodSubarray RPRef.longestGoodSubarray; rfl))
    | (simp only [RPOrig.longestGoodSubarray, RPRef.longestGoodSubarray, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestGoodSubarray RPRef.longestGoodSubarray; rfl))
    | (simp only [RPOrig.longestGoodSubarray, RPRef.longestGoodSubarray, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestGoodSubarray RPRef.longestGoodSubarray; rfl))
    | (simp only [RPOrig.longestGoodSubarray, RPRef.longestGoodSubarray]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestGoodSubarray RPRef.longestGoodSubarray; rfl))

theorem rp_equiv_simp (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) :
    RPOrig.longestGoodSubarray nums k h_precond = RPRef.longestGoodSubarray nums k h_precond := by
  first
    | (simp [RPOrig.longestGoodSubarray, RPRef.longestGoodSubarray, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestGoodSubarray RPRef.longestGoodSubarray; rfl))
    | (simp [RPOrig.longestGoodSubarray, RPRef.longestGoodSubarray, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestGoodSubarray RPRef.longestGoodSubarray; rfl))
    | (simp [RPOrig.longestGoodSubarray, RPRef.longestGoodSubarray, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestGoodSubarray RPRef.longestGoodSubarray; rfl))
    | (simp [RPOrig.longestGoodSubarray, RPRef.longestGoodSubarray]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestGoodSubarray RPRef.longestGoodSubarray; rfl))

theorem rp_equiv_ac_rfl (nums : List Nat) (k : Nat) (h_precond : longestGoodSubarray_precond (nums) (k)) :
    RPOrig.longestGoodSubarray nums k h_precond = RPRef.longestGoodSubarray nums k h_precond := by
  (try simp only [RPOrig.longestGoodSubarray, RPRef.longestGoodSubarray]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestGoodSubarray RPRef.longestGoodSubarray; rfl))
