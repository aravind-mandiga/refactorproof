-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def searchInsert_precond (xs : List Int) (target : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· < ·) xs
  -- !benchmark @end precond



namespace RPOrig

def searchInsert (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) : Nat :=
  match xs with
  | [] =>
      0
  | _ :: _ =>
      let rec helper : List Int → Nat → Nat :=
        fun ys idx =>
          match ys with
          | [] =>
              idx
          | y :: ys' =>
              let isCurrent := y
              let currentIndex := idx
              let targetValue := target
              let condition := targetValue ≤ isCurrent
              if condition then
                currentIndex
              else
                let incrementedIndex := currentIndex + 1
                let rest := ys'
                helper rest incrementedIndex
      let startingIndex := 0
      let result := helper xs startingIndex
      result
end RPOrig

namespace RPRef

def searchInsert (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) : Nat :=
  match xs with
  | [] =>
      0
  | _ :: _ =>
      let rec helper : List Int → Nat → Nat :=
        fun ys idx =>
          match ys with
          | [] =>
              idx
          | y :: ys' =>
              let isCurrent := y
              let currentIndex := idx
              let targetValue := target
              let condition := targetValue ≤ isCurrent
              if condition then
                currentIndex
              else
                let incrementedIndex := 1 + currentIndex
                let rest := ys'
                helper rest incrementedIndex
      let startingIndex := 0
      let result := helper xs startingIndex
      result
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) :
    RPOrig.searchInsert xs target h_precond = RPRef.searchInsert xs target h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) :
    RPOrig.searchInsert xs target h_precond = RPRef.searchInsert xs target h_precond := rfl

theorem rp_equiv_delta_rfl (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) :
    RPOrig.searchInsert xs target h_precond = RPRef.searchInsert xs target h_precond := by
  delta RPOrig.searchInsert RPRef.searchInsert RPOrig.searchInsert.helper RPRef.searchInsert.helper
  rfl

theorem rp_equiv_simp_only (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) :
    RPOrig.searchInsert xs target h_precond = RPRef.searchInsert xs target h_precond := by
  first
    | (simp only [RPOrig.searchInsert, RPRef.searchInsert, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.searchInsert RPRef.searchInsert RPOrig.searchInsert.helper RPRef.searchInsert.helper; rfl))
    | (simp only [RPOrig.searchInsert, RPRef.searchInsert, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.searchInsert RPRef.searchInsert RPOrig.searchInsert.helper RPRef.searchInsert.helper; rfl))
    | (simp only [RPOrig.searchInsert, RPRef.searchInsert, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.searchInsert RPRef.searchInsert RPOrig.searchInsert.helper RPRef.searchInsert.helper; rfl))
    | (simp only [RPOrig.searchInsert, RPRef.searchInsert]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.searchInsert RPRef.searchInsert RPOrig.searchInsert.helper RPRef.searchInsert.helper; rfl))

theorem rp_equiv_simp (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) :
    RPOrig.searchInsert xs target h_precond = RPRef.searchInsert xs target h_precond := by
  first
    | (simp [RPOrig.searchInsert, RPRef.searchInsert, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.searchInsert RPRef.searchInsert RPOrig.searchInsert.helper RPRef.searchInsert.helper; rfl))
    | (simp [RPOrig.searchInsert, RPRef.searchInsert, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.searchInsert RPRef.searchInsert RPOrig.searchInsert.helper RPRef.searchInsert.helper; rfl))
    | (simp [RPOrig.searchInsert, RPRef.searchInsert, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.searchInsert RPRef.searchInsert RPOrig.searchInsert.helper RPRef.searchInsert.helper; rfl))
    | (simp [RPOrig.searchInsert, RPRef.searchInsert]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.searchInsert RPRef.searchInsert RPOrig.searchInsert.helper RPRef.searchInsert.helper; rfl))

theorem rp_equiv_ac_rfl (xs : List Int) (target : Int) (h_precond : searchInsert_precond (xs) (target)) :
    RPOrig.searchInsert xs target h_precond = RPRef.searchInsert xs target h_precond := by
  (try simp only [RPOrig.searchInsert, RPRef.searchInsert]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.searchInsert RPRef.searchInsert RPOrig.searchInsert.helper RPRef.searchInsert.helper; rfl))
