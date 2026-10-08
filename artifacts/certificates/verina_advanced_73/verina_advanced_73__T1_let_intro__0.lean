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
  let __rp_tmp_b7f6d7df : Nat :=
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
  __rp_tmp_b7f6d7df
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
  (simp only [RPOrig.smallestMissing, RPRef.smallestMissing]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissing RPRef.smallestMissing RPOrig.smallestMissing.search RPRef.smallestMissing.search; rfl))

theorem rp_equiv_simp (l : List Nat) (h_precond : smallestMissing_precond (l)) :
    RPOrig.smallestMissing l h_precond = RPRef.smallestMissing l h_precond := by
  (simp [RPOrig.smallestMissing, RPRef.smallestMissing]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.smallestMissing RPRef.smallestMissing RPOrig.smallestMissing.search RPRef.smallestMissing.search; rfl))
