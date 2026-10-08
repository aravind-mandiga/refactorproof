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
          let newK := 1 + k
          countUniques head tail newK
    countUniques init t initCount
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
  first
    | (simp only [RPOrig.removeDuplicates, RPRef.removeDuplicates, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeDuplicates RPRef.removeDuplicates RPOrig.removeDuplicates.countUniques RPRef.removeDuplicates.countUniques; rfl))
    | (simp only [RPOrig.removeDuplicates, RPRef.removeDuplicates, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeDuplicates RPRef.removeDuplicates RPOrig.removeDuplicates.countUniques RPRef.removeDuplicates.countUniques; rfl))
    | (simp only [RPOrig.removeDuplicates, RPRef.removeDuplicates, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeDuplicates RPRef.removeDuplicates RPOrig.removeDuplicates.countUniques RPRef.removeDuplicates.countUniques; rfl))
    | (simp only [RPOrig.removeDuplicates, RPRef.removeDuplicates]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeDuplicates RPRef.removeDuplicates RPOrig.removeDuplicates.countUniques RPRef.removeDuplicates.countUniques; rfl))

theorem rp_equiv_simp (nums : List Int) (h_precond : removeDuplicates_precond (nums)) :
    RPOrig.removeDuplicates nums h_precond = RPRef.removeDuplicates nums h_precond := by
  first
    | (simp [RPOrig.removeDuplicates, RPRef.removeDuplicates, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeDuplicates RPRef.removeDuplicates RPOrig.removeDuplicates.countUniques RPRef.removeDuplicates.countUniques; rfl))
    | (simp [RPOrig.removeDuplicates, RPRef.removeDuplicates, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeDuplicates RPRef.removeDuplicates RPOrig.removeDuplicates.countUniques RPRef.removeDuplicates.countUniques; rfl))
    | (simp [RPOrig.removeDuplicates, RPRef.removeDuplicates, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeDuplicates RPRef.removeDuplicates RPOrig.removeDuplicates.countUniques RPRef.removeDuplicates.countUniques; rfl))
    | (simp [RPOrig.removeDuplicates, RPRef.removeDuplicates]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeDuplicates RPRef.removeDuplicates RPOrig.removeDuplicates.countUniques RPRef.removeDuplicates.countUniques; rfl))

theorem rp_equiv_ac_rfl (nums : List Int) (h_precond : removeDuplicates_precond (nums)) :
    RPOrig.removeDuplicates nums h_precond = RPRef.removeDuplicates nums h_precond := by
  (try simp only [RPOrig.removeDuplicates, RPRef.removeDuplicates]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.removeDuplicates RPRef.removeDuplicates RPOrig.removeDuplicates.countUniques RPRef.removeDuplicates.countUniques; rfl))
