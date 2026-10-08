-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def removeDuplicates_precond (nums : List Int) : Prop :=
  -- !benchmark @start precond
  -- nums are sorted in non-decreasing order
  List.Pairwise (· ≤ ·) nums
  -- !benchmark @end precond



namespace RPOrig

def removeDuplicates (nums : List Int) (h_precond : removeDuplicates_precond (nums)) : Nat :=
  match nums with
  | [] =>
    0
  | h :: t =>
    let init := h
    let initCount := 1
    let rec countUniques (prev : Int) (xs : List Int) (k : Nat) : Nat :=
      match xs with
      | [] =>
        k
      | head :: tail =>
        let isDuplicate := head = prev
        if isDuplicate then
          countUniques prev tail k
        else
          let newK := k + 1
          countUniques head tail newK
    countUniques init t initCount
end RPOrig

namespace RPRef

def removeDuplicates (nums : List Int) (h_precond : removeDuplicates_precond (nums)) : Nat :=
  let __rp_tmp_4cea0d5f : Nat :=
    match nums with
    | [] =>
      0
    | h :: t =>
      let init := h
      let initCount := 1
      let rec countUniques (prev : Int) (xs : List Int) (k : Nat) : Nat :=
        match xs with
        | [] =>
          k
        | head :: tail =>
          let isDuplicate := head = prev
          if isDuplicate then
            countUniques prev tail k
          else
            let newK := k + 1
            countUniques head tail newK
      countUniques init t initCount
  __rp_tmp_4cea0d5f
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (h_precond : removeDuplicates_precond (nums)) :
    RPOrig.removeDuplicates nums h_precond = RPRef.removeDuplicates nums h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (h_precond : removeDuplicates_precond (nums)) :
    RPOrig.removeDuplicates nums h_precond = RPRef.removeDuplicates nums h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (h_precond : removeDuplicates_precond (nums)) :
    RPOrig.removeDuplicates nums h_precond = RPRef.removeDuplicates nums h_precond := by
  delta RPOrig.removeDuplicates RPRef.removeDuplicates RPOrig.removeDuplicates.countUniques RPRef.removeDuplicates.countUniques
  rfl

theorem rp_equiv_simp_only (nums : List Int) (h_precond : removeDuplicates_precond (nums)) :
    RPOrig.removeDuplicates nums h_precond = RPRef.removeDuplicates nums h_precond := by
  (simp only [RPOrig.removeDuplicates, RPRef.removeDuplicates]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeDuplicates RPRef.removeDuplicates RPOrig.removeDuplicates.countUniques RPRef.removeDuplicates.countUniques; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : removeDuplicates_precond (nums)) :
    RPOrig.removeDuplicates nums h_precond = RPRef.removeDuplicates nums h_precond := by
  (simp [RPOrig.removeDuplicates, RPRef.removeDuplicates]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeDuplicates RPRef.removeDuplicates RPOrig.removeDuplicates.countUniques RPRef.removeDuplicates.countUniques; rfl))
