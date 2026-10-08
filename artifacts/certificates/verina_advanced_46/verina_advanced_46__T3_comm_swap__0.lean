-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def maxSubarraySum_precond (numbers : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def maxSubarraySum (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) : Int :=
  let rec isAllNegative : List Int → Bool
    | [] => true
    | x :: xs => if x >= 0 then false else isAllNegative xs

  let rec findMaxProduct : List Int → Int → Int → Int
    | [], currMax, _ => currMax
    | [x], currMax, _ => max currMax x
    | x :: y :: rest, currMax, currSum =>
        let newSum := max y (currSum + y)
        let newMax := max currMax newSum
        findMaxProduct (y :: rest) newMax newSum

  let handleList : List Int → Nat
    | [] => 0
    | xs =>
        if isAllNegative xs then
          0
        else
          match xs with
          | [] => 0
          | x :: rest =>
              let initialMax := max 0 x
              let startSum := max 0 x
              let result := findMaxProduct (x :: rest) initialMax startSum
              result.toNat

  handleList numbers
end RPOrig

namespace RPRef

def maxSubarraySum (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) : Int :=
  let rec isAllNegative : List Int → Bool
    | [] => true
    | x :: xs => if x >= 0 then false else isAllNegative xs

  let rec findMaxProduct : List Int → Int → Int → Int
    | [], currMax, _ => currMax
    | [x], currMax, _ => max currMax x
    | x :: y :: rest, currMax, currSum =>
        let newSum := max y (y + currSum)
        let newMax := max currMax newSum
        findMaxProduct (y :: rest) newMax newSum

  let handleList : List Int → Nat
    | [] => 0
    | xs =>
        if isAllNegative xs then
          0
        else
          match xs with
          | [] => 0
          | x :: rest =>
              let initialMax := max 0 x
              let startSum := max 0 x
              let result := findMaxProduct (x :: rest) initialMax startSum
              result.toNat

  handleList numbers
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    RPOrig.maxSubarraySum numbers h_precond = RPRef.maxSubarraySum numbers h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    RPOrig.maxSubarraySum numbers h_precond = RPRef.maxSubarraySum numbers h_precond := rfl

theorem rp_equiv_delta_rfl (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    RPOrig.maxSubarraySum numbers h_precond = RPRef.maxSubarraySum numbers h_precond := by
  delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.isAllNegative RPOrig.maxSubarraySum.findMaxProduct RPRef.maxSubarraySum.isAllNegative RPRef.maxSubarraySum.findMaxProduct
  rfl

theorem rp_equiv_simp_only (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    RPOrig.maxSubarraySum numbers h_precond = RPRef.maxSubarraySum numbers h_precond := by
  first
    | (simp only [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.isAllNegative RPOrig.maxSubarraySum.findMaxProduct RPRef.maxSubarraySum.isAllNegative RPRef.maxSubarraySum.findMaxProduct; rfl))
    | (simp only [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.isAllNegative RPOrig.maxSubarraySum.findMaxProduct RPRef.maxSubarraySum.isAllNegative RPRef.maxSubarraySum.findMaxProduct; rfl))
    | (simp only [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.isAllNegative RPOrig.maxSubarraySum.findMaxProduct RPRef.maxSubarraySum.isAllNegative RPRef.maxSubarraySum.findMaxProduct; rfl))
    | (simp only [RPOrig.maxSubarraySum, RPRef.maxSubarraySum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.isAllNegative RPOrig.maxSubarraySum.findMaxProduct RPRef.maxSubarraySum.isAllNegative RPRef.maxSubarraySum.findMaxProduct; rfl))

theorem rp_equiv_simp (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    RPOrig.maxSubarraySum numbers h_precond = RPRef.maxSubarraySum numbers h_precond := by
  first
    | (simp [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.isAllNegative RPOrig.maxSubarraySum.findMaxProduct RPRef.maxSubarraySum.isAllNegative RPRef.maxSubarraySum.findMaxProduct; rfl))
    | (simp [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.isAllNegative RPOrig.maxSubarraySum.findMaxProduct RPRef.maxSubarraySum.isAllNegative RPRef.maxSubarraySum.findMaxProduct; rfl))
    | (simp [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.isAllNegative RPOrig.maxSubarraySum.findMaxProduct RPRef.maxSubarraySum.isAllNegative RPRef.maxSubarraySum.findMaxProduct; rfl))
    | (simp [RPOrig.maxSubarraySum, RPRef.maxSubarraySum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.isAllNegative RPOrig.maxSubarraySum.findMaxProduct RPRef.maxSubarraySum.isAllNegative RPRef.maxSubarraySum.findMaxProduct; rfl))

theorem rp_equiv_ac_rfl (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    RPOrig.maxSubarraySum numbers h_precond = RPRef.maxSubarraySum numbers h_precond := by
  (try simp only [RPOrig.maxSubarraySum, RPRef.maxSubarraySum]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPOrig.maxSubarraySum.isAllNegative RPOrig.maxSubarraySum.findMaxProduct RPRef.maxSubarraySum.isAllNegative RPRef.maxSubarraySum.findMaxProduct; rfl))
