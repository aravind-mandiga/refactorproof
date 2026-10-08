-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def mergeIntervals_precond (intervals : List (Prod Int Int)) : Prop :=
  -- !benchmark @start precond
  intervals.all (fun (s, e) => s ≤ e)
  -- !benchmark @end precond



namespace RPOrig

def mergeIntervals (intervals : List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) : List (Prod Int Int) :=
  -- Insertion sort based on the start of intervals
  let rec insert (x : Prod Int Int) (sorted : List (Prod Int Int)) : List (Prod Int Int) :=
    match sorted with
    | [] => [x]
    | y :: ys => if x.fst ≤ y.fst then x :: sorted else y :: insert x ys

  let rec sort (xs : List (Prod Int Int)) : List (Prod Int Int) :=
    match xs with
    | [] => []
    | x :: xs' => insert x (sort xs')

  let sorted := sort intervals

  -- Merge sorted intervals
  let rec merge (xs : List (Prod Int Int)) (acc : List (Prod Int Int)) : List (Prod Int Int) :=
    match xs, acc with
    | [], _ => acc.reverse
    | (s, e) :: rest, [] => merge rest [(s, e)]
    | (s, e) :: rest, (ps, pe) :: accTail =>
      if s ≤ pe then
        merge rest ((ps, max pe e) :: accTail)
      else
        merge rest ((s, e) :: (ps, pe) :: accTail)

  merge sorted []
end RPOrig

namespace RPRef

def mergeIntervals (intervals : List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) : List (Prod Int Int) :=
  let __rp_tmp_1074bbe0 : List (Prod Int Int) :=
    -- Insertion sort based on the start of intervals
    let rec insert (x : Prod Int Int) (sorted : List (Prod Int Int)) : List (Prod Int Int) :=
      match sorted with
      | [] => [x]
      | y :: ys => if x.fst ≤ y.fst then x :: sorted else y :: insert x ys

    let rec sort (xs : List (Prod Int Int)) : List (Prod Int Int) :=
      match xs with
      | [] => []
      | x :: xs' => insert x (sort xs')

    let sorted := sort intervals

    -- Merge sorted intervals
    let rec merge (xs : List (Prod Int Int)) (acc : List (Prod Int Int)) : List (Prod Int Int) :=
      match xs, acc with
      | [], _ => acc.reverse
      | (s, e) :: rest, [] => merge rest [(s, e)]
      | (s, e) :: rest, (ps, pe) :: accTail =>
        if s ≤ pe then
          merge rest ((ps, max pe e) :: accTail)
        else
          merge rest ((s, e) :: (ps, pe) :: accTail)

    merge sorted []
  __rp_tmp_1074bbe0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (intervals : List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) :
    RPOrig.mergeIntervals intervals h_precond = RPRef.mergeIntervals intervals h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (intervals : List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) :
    RPOrig.mergeIntervals intervals h_precond = RPRef.mergeIntervals intervals h_precond := rfl

theorem rp_equiv_delta_rfl (intervals : List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) :
    RPOrig.mergeIntervals intervals h_precond = RPRef.mergeIntervals intervals h_precond := by
  delta RPOrig.mergeIntervals RPRef.mergeIntervals RPOrig.mergeIntervals.insert RPOrig.mergeIntervals.sort RPOrig.mergeIntervals.merge RPRef.mergeIntervals.insert RPRef.mergeIntervals.sort RPRef.mergeIntervals.merge
  rfl

theorem rp_equiv_simp_only (intervals : List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) :
    RPOrig.mergeIntervals intervals h_precond = RPRef.mergeIntervals intervals h_precond := by
  (simp only [RPOrig.mergeIntervals, RPRef.mergeIntervals]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.mergeIntervals RPRef.mergeIntervals RPOrig.mergeIntervals.insert RPOrig.mergeIntervals.sort RPOrig.mergeIntervals.merge RPRef.mergeIntervals.insert RPRef.mergeIntervals.sort RPRef.mergeIntervals.merge; rfl))

theorem rp_equiv_simp (intervals : List (Prod Int Int)) (h_precond : mergeIntervals_precond (intervals)) :
    RPOrig.mergeIntervals intervals h_precond = RPRef.mergeIntervals intervals h_precond := by
  (simp [RPOrig.mergeIntervals, RPRef.mergeIntervals]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.mergeIntervals RPRef.mergeIntervals RPOrig.mergeIntervals.insert RPOrig.mergeIntervals.sort RPOrig.mergeIntervals.merge RPRef.mergeIntervals.insert RPRef.mergeIntervals.sort RPRef.mergeIntervals.merge; rfl))
