-- !benchmark @start import type=solution
import Std.Data.HashSet
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux
open Std
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def longestConsecutive_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  List.Nodup nums
  -- !benchmark @end precond



namespace RPOrig

def longestConsecutive (nums : List Int) (h_precond : longestConsecutive_precond (nums)) : Nat :=
  Id.run do
    let mut set := HashSet.emptyWithCapacity
    for x in nums do
      set := set.insert x

    let mut maxLen := 0

    for x in nums do
      if !set.contains (x - 1) then
        let mut curr := x
        let mut length := 1
        for _ in List.range nums.length do
          if set.contains (curr + 1) then
            curr := curr + 1
            length := length + 1
          else
            break
        maxLen := Nat.max maxLen length

    return maxLen
end RPOrig

namespace RPRef

def longestConsecutive (nums : List Int) (h_precond : longestConsecutive_precond (nums)) : Nat :=
  Id.run do
    let mut set := HashSet.emptyWithCapacity
    for x in nums do
      set := set.insert x

    let mut maxLen := 0

    for x in nums do
      if !set.contains (x - 1) then
        let mut curr := x
        let mut length := 1
        for _ in List.range nums.length do
          if set.contains (1 + curr) then
            curr := curr + 1
            length := length + 1
          else
            break
        maxLen := Nat.max maxLen length

    return maxLen
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : longestConsecutive_precond (nums)) :
    RPOrig.longestConsecutive nums h_precond = RPRef.longestConsecutive nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : longestConsecutive_precond (nums)) :
    RPOrig.longestConsecutive nums h_precond = RPRef.longestConsecutive nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : longestConsecutive_precond (nums)) :
    RPOrig.longestConsecutive nums h_precond = RPRef.longestConsecutive nums h_precond := by
  delta RPOrig.longestConsecutive RPRef.longestConsecutive
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : longestConsecutive_precond (nums)) :
    RPOrig.longestConsecutive nums h_precond = RPRef.longestConsecutive nums h_precond := by
  first
    | (simp only [RPOrig.longestConsecutive, RPRef.longestConsecutive, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestConsecutive RPRef.longestConsecutive; rfl))
    | (simp only [RPOrig.longestConsecutive, RPRef.longestConsecutive, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestConsecutive RPRef.longestConsecutive; rfl))
    | (simp only [RPOrig.longestConsecutive, RPRef.longestConsecutive, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestConsecutive RPRef.longestConsecutive; rfl))
    | (simp only [RPOrig.longestConsecutive, RPRef.longestConsecutive]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestConsecutive RPRef.longestConsecutive; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : longestConsecutive_precond (nums)) :
    RPOrig.longestConsecutive nums h_precond = RPRef.longestConsecutive nums h_precond := by
  first
    | (simp [RPOrig.longestConsecutive, RPRef.longestConsecutive, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestConsecutive RPRef.longestConsecutive; rfl))
    | (simp [RPOrig.longestConsecutive, RPRef.longestConsecutive, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestConsecutive RPRef.longestConsecutive; rfl))
    | (simp [RPOrig.longestConsecutive, RPRef.longestConsecutive, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestConsecutive RPRef.longestConsecutive; rfl))
    | (simp [RPOrig.longestConsecutive, RPRef.longestConsecutive]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestConsecutive RPRef.longestConsecutive; rfl))

theorem rp_equiv_ac_rfl (nums : List Int) (h_precond : longestConsecutive_precond (nums)) :
    RPOrig.longestConsecutive nums h_precond = RPRef.longestConsecutive nums h_precond := by
  (try simp only [RPOrig.longestConsecutive, RPRef.longestConsecutive]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestConsecutive RPRef.longestConsecutive; rfl))
