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
private def maxSubarraySum__rp_helper_b8cb03bf (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) : Int :=
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

def maxSubarraySum (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) : Int :=
  maxSubarraySum__rp_helper_b8cb03bf numbers h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    RPOrig.maxSubarraySum numbers h_precond = RPRef.maxSubarraySum numbers h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    RPOrig.maxSubarraySum numbers h_precond = RPRef.maxSubarraySum numbers h_precond := rfl

theorem rp_equiv_delta_rfl (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    RPOrig.maxSubarraySum numbers h_precond = RPRef.maxSubarraySum numbers h_precond := by
  delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPRef.maxSubarraySum__rp_helper_b8cb03bf RPOrig.maxSubarraySum.isAllNegative RPOrig.maxSubarraySum.findMaxProduct RPRef.maxSubarraySum__rp_helper_b8cb03bf.isAllNegative RPRef.maxSubarraySum__rp_helper_b8cb03bf.findMaxProduct
  rfl

theorem rp_equiv_simp_only (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    RPOrig.maxSubarraySum numbers h_precond = RPRef.maxSubarraySum numbers h_precond := by
  (simp only [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, RPRef.maxSubarraySum__rp_helper_b8cb03bf]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPRef.maxSubarraySum__rp_helper_b8cb03bf RPOrig.maxSubarraySum.isAllNegative RPOrig.maxSubarraySum.findMaxProduct RPRef.maxSubarraySum__rp_helper_b8cb03bf.isAllNegative RPRef.maxSubarraySum__rp_helper_b8cb03bf.findMaxProduct; rfl))

theorem rp_equiv_simp (numbers : List Int) (h_precond : maxSubarraySum_precond (numbers)) :
    RPOrig.maxSubarraySum numbers h_precond = RPRef.maxSubarraySum numbers h_precond := by
  (simp [RPOrig.maxSubarraySum, RPRef.maxSubarraySum, RPRef.maxSubarraySum__rp_helper_b8cb03bf]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxSubarraySum RPRef.maxSubarraySum RPRef.maxSubarraySum__rp_helper_b8cb03bf RPOrig.maxSubarraySum.isAllNegative RPOrig.maxSubarraySum.findMaxProduct RPRef.maxSubarraySum__rp_helper_b8cb03bf.isAllNegative RPRef.maxSubarraySum__rp_helper_b8cb03bf.findMaxProduct; rfl))
