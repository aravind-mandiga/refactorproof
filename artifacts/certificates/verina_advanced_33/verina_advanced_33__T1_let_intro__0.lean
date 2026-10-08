-- !benchmark @start import type=solution
import Mathlib.Data.List.Basic
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def longestIncreasingSubsequence_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Nat :=
  let max2 (a : Nat) (b : Nat) : Nat :=
    if a > b then a else b

  let rec listLength (l : List Int) : Nat :=
    match l with
    | []      => 0
    | _ :: xs => 1 + listLength xs

  let rec helper (lst : List Int) (prev : Option Int) : Nat :=
    match lst with
    | [] => 0
    | h :: t =>
        let canTake : Bool :=
          if prev = none then true
          else if prev.get! < h then true else false
        let withTake : Nat :=
          if canTake then 1 + helper t (some h) else 0
        let withoutTake : Nat := helper t prev
        max2 withTake withoutTake

  let result := helper nums none
  result
end RPOrig

namespace RPRef

def longestIncreasingSubsequence (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) : Nat :=
  let __rp_tmp_ea999820 : Nat :=
    let max2 (a : Nat) (b : Nat) : Nat :=
      if a > b then a else b

    let rec listLength (l : List Int) : Nat :=
      match l with
      | []      => 0
      | _ :: xs => 1 + listLength xs

    let rec helper (lst : List Int) (prev : Option Int) : Nat :=
      match lst with
      | [] => 0
      | h :: t =>
          let canTake : Bool :=
            if prev = none then true
            else if prev.get! < h then true else false
          let withTake : Nat :=
            if canTake then 1 + helper t (some h) else 0
          let withoutTake : Nat := helper t prev
          max2 withTake withoutTake

    let result := helper nums none
    result
  __rp_tmp_ea999820
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    RPOrig.longestIncreasingSubsequence nums h_precond = RPRef.longestIncreasingSubsequence nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    RPOrig.longestIncreasingSubsequence nums h_precond = RPRef.longestIncreasingSubsequence nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    RPOrig.longestIncreasingSubsequence nums h_precond = RPRef.longestIncreasingSubsequence nums h_precond := by
  delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.listLength RPOrig.longestIncreasingSubsequence.helper RPRef.longestIncreasingSubsequence.listLength RPRef.longestIncreasingSubsequence.helper
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    RPOrig.longestIncreasingSubsequence nums h_precond = RPRef.longestIncreasingSubsequence nums h_precond := by
  (simp only [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.listLength RPOrig.longestIncreasingSubsequence.helper RPRef.longestIncreasingSubsequence.listLength RPRef.longestIncreasingSubsequence.helper; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : longestIncreasingSubsequence_precond (nums)) :
    RPOrig.longestIncreasingSubsequence nums h_precond = RPRef.longestIncreasingSubsequence nums h_precond := by
  (simp [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.listLength RPOrig.longestIncreasingSubsequence.helper RPRef.longestIncreasingSubsequence.listLength RPRef.longestIncreasingSubsequence.helper; rfl))
