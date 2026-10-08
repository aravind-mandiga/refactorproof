-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def semiOrderedPermutation_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  let n := nums.length
  n > 0 ∧
  -- Must be a permutation of [1..n]: all distinct, all in range
  List.Nodup nums ∧
  nums.all (fun x => 1 ≤ x ∧ x ≤ Int.ofNat n)
  -- !benchmark @end precond



namespace RPOrig

def semiOrderedPermutation (nums : List Int) (h_precond : semiOrderedPermutation_precond (nums)) : Int :=
  let lengthList := nums.length
  let numOne : Int := 1
  let largestNum : Int := Int.ofNat lengthList

  let firstIndex := nums.idxOf numOne
  let lastIndex := nums.idxOf largestNum

  let startPosition := 0
  let endPosition := lengthList - 1

  let shouldMoveOne := firstIndex != startPosition
  let shouldMoveLast := lastIndex != endPosition

  let distanceOne := if shouldMoveOne then firstIndex else 0
  let distanceLast := if shouldMoveLast then endPosition - lastIndex else 0

  let totalMoves := distanceOne + distanceLast
  let needAdjustment := firstIndex > lastIndex
  let adjustedMoves := if needAdjustment then totalMoves - 1 else totalMoves

  adjustedMoves
end RPOrig

namespace RPRef
private def semiOrderedPermutation__rp_helper_37cd6f2d (nums : List Int) (h_precond : semiOrderedPermutation_precond (nums)) : Int :=
  let lengthList := nums.length
  let numOne : Int := 1
  let largestNum : Int := Int.ofNat lengthList

  let firstIndex := nums.idxOf numOne
  let lastIndex := nums.idxOf largestNum

  let startPosition := 0
  let endPosition := lengthList - 1

  let shouldMoveOne := firstIndex != startPosition
  let shouldMoveLast := lastIndex != endPosition

  let distanceOne := if shouldMoveOne then firstIndex else 0
  let distanceLast := if shouldMoveLast then endPosition - lastIndex else 0

  let totalMoves := distanceOne + distanceLast
  let needAdjustment := firstIndex > lastIndex
  let adjustedMoves := if needAdjustment then totalMoves - 1 else totalMoves

  adjustedMoves

def semiOrderedPermutation (nums : List Int) (h_precond : semiOrderedPermutation_precond (nums)) : Int :=
  semiOrderedPermutation__rp_helper_37cd6f2d nums h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : semiOrderedPermutation_precond (nums)) :
    RPOrig.semiOrderedPermutation nums h_precond = RPRef.semiOrderedPermutation nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : semiOrderedPermutation_precond (nums)) :
    RPOrig.semiOrderedPermutation nums h_precond = RPRef.semiOrderedPermutation nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : semiOrderedPermutation_precond (nums)) :
    RPOrig.semiOrderedPermutation nums h_precond = RPRef.semiOrderedPermutation nums h_precond := by
  delta RPOrig.semiOrderedPermutation RPRef.semiOrderedPermutation RPRef.semiOrderedPermutation__rp_helper_37cd6f2d
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : semiOrderedPermutation_precond (nums)) :
    RPOrig.semiOrderedPermutation nums h_precond = RPRef.semiOrderedPermutation nums h_precond := by
  (simp only [RPOrig.semiOrderedPermutation, RPRef.semiOrderedPermutation, RPRef.semiOrderedPermutation__rp_helper_37cd6f2d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.semiOrderedPermutation RPRef.semiOrderedPermutation RPRef.semiOrderedPermutation__rp_helper_37cd6f2d; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : semiOrderedPermutation_precond (nums)) :
    RPOrig.semiOrderedPermutation nums h_precond = RPRef.semiOrderedPermutation nums h_precond := by
  (simp [RPOrig.semiOrderedPermutation, RPRef.semiOrderedPermutation, RPRef.semiOrderedPermutation__rp_helper_37cd6f2d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.semiOrderedPermutation RPRef.semiOrderedPermutation RPRef.semiOrderedPermutation__rp_helper_37cd6f2d; rfl))
