-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def smallestMissing_precond (l : List Nat) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· < ·) l
  -- !benchmark @end precond



namespace RPOrig

def smallestMissing (l : List Nat) (h_precond : smallestMissing_precond (l)) : Nat :=
  let sortedList := l
  let rec search (lst : List Nat) (n : Nat) : Nat :=
    match lst with
    | [] => n
    | x :: xs =>
      let isEqual := x = n
      let isGreater := x > n
      let nextCand := n + 1
      if isEqual then
        search xs nextCand
      else if isGreater then
        n
      else
        search xs n
  let result := search sortedList 0
  result
end RPOrig

namespace RPRef

def smallestMissing (l : List Nat) (h_precond : smallestMissing_precond (l)) : Nat :=
  let sortedList := l
  let rec search (lst : List Nat) (n : Nat) : Nat :=
    match lst with
    | [] => n
    | x :: xs =>
      let isEqual := x = n
      let isGreater := x > n
      let nextCand := 1 + n
      if isEqual then
        search xs nextCand
      else if isGreater then
        n
      else
        search xs n
  let result := search sortedList 0
  result
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (l : List Nat) (h_precond : smallestMissing_precond (l)) :
    RPOrig.smallestMissing l h_precond = RPRef.smallestMissing l h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (l : List Nat) (h_precond : smallestMissing_precond (l)) :
    RPOrig.smallestMissing l h_precond = RPRef.smallestMissing l h_precond := rfl

theorem rp_equiv_delta_rfl (l : List Nat) (h_precond : smallestMissing_precond (l)) :
    RPOrig.smallestMissing l h_precond = RPRef.smallestMissing l h_precond := by
  delta RPOrig.smallestMissing RPRef.smallestMissing RPOrig.smallestMissing.search RPRef.smallestMissing.search
  rfl

theorem rp_equiv_simp_only (l : List Nat) (h_precond : smallestMissing_precond (l)) :
    RPOrig.smallestMissing l h_precond = RPRef.smallestMissing l h_precond := by
  first
    | (simp only [RPOrig.smallestMissing, RPRef.smallestMissing, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissing RPRef.smallestMissing RPOrig.smallestMissing.search RPRef.smallestMissing.search; rfl))
    | (simp only [RPOrig.smallestMissing, RPRef.smallestMissing, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissing RPRef.smallestMissing RPOrig.smallestMissing.search RPRef.smallestMissing.search; rfl))
    | (simp only [RPOrig.smallestMissing, RPRef.smallestMissing, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissing RPRef.smallestMissing RPOrig.smallestMissing.search RPRef.smallestMissing.search; rfl))
    | (simp only [RPOrig.smallestMissing, RPRef.smallestMissing]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissing RPRef.smallestMissing RPOrig.smallestMissing.search RPRef.smallestMissing.search; rfl))

theorem rp_equiv_simp (l : List Nat) (h_precond : smallestMissing_precond (l)) :
    RPOrig.smallestMissing l h_precond = RPRef.smallestMissing l h_precond := by
  first
    | (simp [RPOrig.smallestMissing, RPRef.smallestMissing, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissing RPRef.smallestMissing RPOrig.smallestMissing.search RPRef.smallestMissing.search; rfl))
    | (simp [RPOrig.smallestMissing, RPRef.smallestMissing, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissing RPRef.smallestMissing RPOrig.smallestMissing.search RPRef.smallestMissing.search; rfl))
    | (simp [RPOrig.smallestMissing, RPRef.smallestMissing, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissing RPRef.smallestMissing RPOrig.smallestMissing.search RPRef.smallestMissing.search; rfl))
    | (simp [RPOrig.smallestMissing, RPRef.smallestMissing]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissing RPRef.smallestMissing RPOrig.smallestMissing.search RPRef.smallestMissing.search; rfl))

theorem rp_equiv_ac_rfl (l : List Nat) (h_precond : smallestMissing_precond (l)) :
    RPOrig.smallestMissing l h_precond = RPRef.smallestMissing l h_precond := by
  (try simp only [RPOrig.smallestMissing, RPRef.smallestMissing]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissing RPRef.smallestMissing RPOrig.smallestMissing.search RPRef.smallestMissing.search; rfl))
