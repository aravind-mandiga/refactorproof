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
  let __rp_tmp_164ea82d : Nat :=
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
  __rp_tmp_164ea82d
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
  (simp only [RPOrig.longestConsecutive, RPRef.longestConsecutive]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestConsecutive RPRef.longestConsecutive; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : longestConsecutive_precond (nums)) :
    RPOrig.longestConsecutive nums h_precond = RPRef.longestConsecutive nums h_precond := by
  (simp [RPOrig.longestConsecutive, RPRef.longestConsecutive]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestConsecutive RPRef.longestConsecutive; rfl))
