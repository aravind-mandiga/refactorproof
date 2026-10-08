-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def filterlist (x : Int) (nums : List Int) : List Int :=
  let rec aux (lst : List Int) : List Int :=
    match lst with
    | []      => []
    | y :: ys => if y = x then y :: aux ys else aux ys
  aux nums
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def FindSingleNumber_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  let numsCount := nums.map (fun x => nums.count x)
  numsCount.all (fun count => count = 1 ∨ count = 2) ∧ numsCount.count 1 = 1
  -- !benchmark @end precond



namespace RPOrig

def FindSingleNumber (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) : Int :=
  let rec findUnique (remaining : List Int) : Int :=
    match remaining with
    | [] =>
      0
    | x :: xs =>
      let filtered : List Int :=
        filterlist x nums
      let count : Nat :=
        filtered.length
      if count = 1 then
        x
      else
        findUnique xs
  findUnique nums
end RPOrig

namespace RPRef

private def FindSingleNumber__rp_helper_cec7bc45 (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) : Int :=
  let rec findUnique (remaining : List Int) : Int :=
    match remaining with
    | [] =>
      0
    | x :: xs =>
      let filtered : List Int :=
        filterlist x nums
      let count : Nat :=
        filtered.length
      if count = 1 then
        x
      else
        findUnique xs
  findUnique nums

def FindSingleNumber (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) : Int :=
  FindSingleNumber__rp_helper_cec7bc45 nums h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) :
    RPOrig.FindSingleNumber nums h_precond = RPRef.FindSingleNumber nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) :
    RPOrig.FindSingleNumber nums h_precond = RPRef.FindSingleNumber nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) :
    RPOrig.FindSingleNumber nums h_precond = RPRef.FindSingleNumber nums h_precond := by
  delta RPOrig.FindSingleNumber RPRef.FindSingleNumber RPRef.FindSingleNumber__rp_helper_cec7bc45 RPOrig.FindSingleNumber.findUnique RPRef.FindSingleNumber__rp_helper_cec7bc45.findUnique
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) :
    RPOrig.FindSingleNumber nums h_precond = RPRef.FindSingleNumber nums h_precond := by
  (simp only [RPOrig.FindSingleNumber, RPRef.FindSingleNumber, RPRef.FindSingleNumber__rp_helper_cec7bc45]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.FindSingleNumber RPRef.FindSingleNumber RPRef.FindSingleNumber__rp_helper_cec7bc45 RPOrig.FindSingleNumber.findUnique RPRef.FindSingleNumber__rp_helper_cec7bc45.findUnique; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : FindSingleNumber_precond (nums)) :
    RPOrig.FindSingleNumber nums h_precond = RPRef.FindSingleNumber nums h_precond := by
  (simp [RPOrig.FindSingleNumber, RPRef.FindSingleNumber, RPRef.FindSingleNumber__rp_helper_cec7bc45]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.FindSingleNumber RPRef.FindSingleNumber RPRef.FindSingleNumber__rp_helper_cec7bc45 RPOrig.FindSingleNumber.findUnique RPRef.FindSingleNumber__rp_helper_cec7bc45.findUnique; rfl))
