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
        let currLength := 1 + bestPrevLen
        buildTables restNums (prevNums ++ [currNum]) (lengths ++ [currLength]) (idx + 1)

  match numbers with
  | [] => 0
  | [x] => 1
  | first :: rest => buildTables rest [first] [1] 1
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) :
    RPOrig.longestIncreasingSubsequence numbers h_precond = RPRef.longestIncreasingSubsequence numbers h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) :
    RPOrig.longestIncreasingSubsequence numbers h_precond = RPRef.longestIncreasingSubsequence numbers h_precond := rfl

theorem rp_equiv_delta_rfl (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) :
    RPOrig.longestIncreasingSubsequence numbers h_precond = RPRef.longestIncreasingSubsequence numbers h_precond := by
  first
    | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr; rfl)
    | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPOrig.longestIncreasingSubsequence._unary RPOrig.longestIncreasingSubsequence.buildTables._unary RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary RPRef.longestIncreasingSubsequence.buildTables._unary RPRef.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary; rfl)
    | (set_option smartUnfolding false in rfl)

theorem rp_equiv_simp_only (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) :
    RPOrig.longestIncreasingSubsequence numbers h_precond = RPRef.longestIncreasingSubsequence numbers h_precond := by
  first
    | (simp only [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr; rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPOrig.longestIncreasingSubsequence._unary RPOrig.longestIncreasingSubsequence.buildTables._unary RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary RPRef.longestIncreasingSubsequence.buildTables._unary RPRef.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp only [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr; rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPOrig.longestIncreasingSubsequence._unary RPOrig.longestIncreasingSubsequence.buildTables._unary RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary RPRef.longestIncreasingSubsequence.buildTables._unary RPRef.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp only [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr; rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPOrig.longestIncreasingSubsequence._unary RPOrig.longestIncreasingSubsequence.buildTables._unary RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary RPRef.longestIncreasingSubsequence.buildTables._unary RPRef.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp only [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence]) <;> (first | rfl | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr; rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPOrig.longestIncreasingSubsequence._unary RPOrig.longestIncreasingSubsequence.buildTables._unary RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary RPRef.longestIncreasingSubsequence.buildTables._unary RPRef.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_simp (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) :
    RPOrig.longestIncreasingSubsequence numbers h_precond = RPRef.longestIncreasingSubsequence numbers h_precond := by
  first
    | (simp [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr; rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPOrig.longestIncreasingSubsequence._unary RPOrig.longestIncreasingSubsequence.buildTables._unary RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary RPRef.longestIncreasingSubsequence.buildTables._unary RPRef.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr; rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPOrig.longestIncreasingSubsequence._unary RPOrig.longestIncreasingSubsequence.buildTables._unary RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary RPRef.longestIncreasingSubsequence.buildTables._unary RPRef.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr; rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPOrig.longestIncreasingSubsequence._unary RPOrig.longestIncreasingSubsequence.buildTables._unary RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary RPRef.longestIncreasingSubsequence.buildTables._unary RPRef.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary; rfl) | (set_option smartUnfolding false in rfl))
    | (simp [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence]) <;> (first | rfl | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr; rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPOrig.longestIncreasingSubsequence._unary RPOrig.longestIncreasingSubsequence.buildTables._unary RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary RPRef.longestIncreasingSubsequence.buildTables._unary RPRef.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_ac_rfl (numbers : List Int) (h_precond : longestIncreasingSubsequence_precond (numbers)) :
    RPOrig.longestIncreasingSubsequence numbers h_precond = RPRef.longestIncreasingSubsequence numbers h_precond := by
  (try simp only [RPOrig.longestIncreasingSubsequence, RPRef.longestIncreasingSubsequence]) <;> (try ac_nf) <;> (first | rfl | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr; rfl) | (delta RPOrig.longestIncreasingSubsequence RPRef.longestIncreasingSubsequence RPOrig.longestIncreasingSubsequence.buildTables RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPRef.longestIncreasingSubsequence.buildTables RPRef.longestIncreasingSubsequence.buildTables.findMaxLength RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr RPOrig.longestIncreasingSubsequence._unary RPOrig.longestIncreasingSubsequence.buildTables._unary RPOrig.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPOrig.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary RPRef.longestIncreasingSubsequence.buildTables._unary RPRef.longestIncreasingSubsequence.buildTables.findMaxLength._unary RPRef.longestIncreasingSubsequence.buildTables.findLengthEndingAtCurr._unary; rfl) | (set_option smartUnfolding false in rfl))
