-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def longestIncreasingSubsequence_precond (numbers : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def longestIncreasingSubsequence (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) : Nat :=
  let rec buildTables : List Int → List Int → List Nat → Nat → Nat
    | [], _, lengths, _ =>
        let rec findMaxLength : List Nat → Nat
          | [] => 0
          | x :: xs =>
              let maxRest := findMaxLength xs
              if x > maxRest then x else maxRest
        findMaxLength lengths
    | currNum :: restNums, prevNums, lengths, idx =>
        let rec findLengthEndingAtCurr : List Int → List Nat → Nat → Nat
          | [], _, best => best
          | prevVal :: restVals, prevLen :: restLens, best =>
              if prevVal < currNum then
                findLengthEndingAtCurr restVals restLens (max best prevLen)
              else
                findLengthEndingAtCurr restVals restLens best
          | _, _, best => best

        let bestPrevLen := findLengthEndingAtCurr prevNums lengths 0
        let currLength := bestPrevLen + 1
        buildTables restNums (prevNums ++ [currNum]) (lengths ++ [currLength]) (idx + 1)

  match numbers with
  | [] => 0
  | [x] => 1
  | first :: rest => buildTables rest [first] [1] 1
end RPOrig

namespace RPRef
private def longestIncreasingSubsequence__rp_helper_88436887 (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) : Nat :=
  let rec buildTables : List Int → List Int → List Nat → Nat → Nat
    | [], _, lengths, _ =>
        let rec findMaxLength : List Nat → Nat
          | [] => 0
          | x :: xs =>
              let maxRest := findMaxLength xs
              if x > maxRest then x else maxRest
        findMaxLength lengths
    | currNum :: restNums, prevNums, lengths, idx =>
        let rec findLengthEndingAtCurr : List Int → List Nat → Nat → Nat
          | [], _, best => best
          | prevVal :: restVals, prevLen :: restLens, best =>
              if prevVal < currNum then
                findLengthEndingAtCurr restVals restLens (max best prevLen)
              else
                findLengthEndingAtCurr restVals restLens best
          | _, _, best => best

        let bestPrevLen := findLengthEndingAtCurr prevNums lengths 0
        let currLength := bestPrevLen + 1
        buildTables restNums (prevNums ++ [currNum]) (lengths ++ [currLength]) (idx + 1)

  match numbers with
  | [] => 0
  | [x] => 1
  | first :: rest => buildTables rest [first] [1] 1

def longestIncreasingSubsequence (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) : Nat :=
  longestIncreasingSubsequence__rp_helper_88436887 numbers h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) :
    RPOrig.longestIncreasingSubsequence numbers h_precond = RPRef.longestIncreasingSubsequence numbers h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) :
    RPOrig.longestIncreasingSubsequence numbers h_precond = RPRef.longestIncreasingSubsequence numbers h_precond := rfl

theorem rp_equiv_delta_rfl (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) :
    RPOrig.longestIncreasingSubsequence numbers h_precond = RPRef.longestIncreasingSubsequence numbers h_precond := by
  delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence__rp_helper_88436887 RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.findMaxLength RPOrig.longestIncreasingSubsequence.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence__rp_helper_88436887.buildTables RPRef.longestIncreasingSubsequence__rp_helper_88436887.findMaxLength RPRef.longestIncreasingSubsequence__rp_helper_88436887.findLengthEndingAtCurr
  rfl

theorem rp_equiv_simp_only (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) :
    RPOrig.longestIncreasingSubsequence numbers h_precond = RPRef.longestIncreasingSubsequence numbers h_precond := by
  (simp only [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence__rp_helper_88436887]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence__rp_helper_88436887 RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.findMaxLength RPOrig.longestIncreasingSubsequence.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence__rp_helper_88436887.buildTables RPRef.longestIncreasingSubsequence__rp_helper_88436887.findMaxLength RPRef.longestIncreasingSubsequence__rp_helper_88436887.findLengthEndingAtCurr; rfl))

theorem rp_equiv_simp (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) :
    RPOrig.longestIncreasingSubsequence numbers h_precond = RPRef.longestIncreasingSubsequence numbers h_precond := by
  (simp [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence__rp_helper_88436887]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence__rp_helper_88436887 RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.findMaxLength RPOrig.longestIncreasingSubsequence.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence__rp_helper_88436887.buildTables RPRef.longestIncreasingSubsequence__rp_helper_88436887.findMaxLength RPRef.longestIncreasingSubsequence__rp_helper_88436887.findLengthEndingAtCurr; rfl))
