-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def maxCoverageAfterRemovingOne_precond (intervals : List (Prod Nat Nat)) : Prop :=
  -- !benchmark @start precond
  intervals.length > 0
  -- !benchmark @end precond



namespace RPOrig

def maxCoverageAfterRemovingOne (intervals : List (Prod Nat Nat)) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) : Nat :=
  let n := intervals.length
  if n ≤ 1 then 0
  else
    (List.range n).foldl (fun acc i =>
      let remaining := List.eraseIdx intervals i
      let sorted := List.mergeSort remaining (fun (a b : Nat × Nat) => a.1 ≤ b.1)
      let merged := sorted.foldl (fun acc curr =>
        match acc with
        | [] => [curr]
        | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
      ) []
      let coverage := merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
      max acc coverage
    ) 0
end RPOrig

namespace RPRef

def maxCoverageAfterRemovingOne (intervals : List (Prod Nat Nat)) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) : Nat :=
  let __rp_tmp_73251cad : Nat :=
    let n := intervals.length
    if n ≤ 1 then 0
    else
      (List.range n).foldl (fun acc i =>
        let remaining := List.eraseIdx intervals i
        let sorted := List.mergeSort remaining (fun (a b : Nat × Nat) => a.1 ≤ b.1)
        let merged := sorted.foldl (fun acc curr =>
          match acc with
          | [] => [curr]
          | (s, e) :: rest => if curr.1 ≤ e then (s, max e curr.2) :: rest else curr :: acc
        ) []
        let coverage := merged.reverse.foldl (fun acc (s, e) => acc + (e - s)) 0
        max acc coverage
      ) 0
  __rp_tmp_73251cad
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (intervals : List (Prod Nat Nat)) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) :
    RPOrig.maxCoverageAfterRemovingOne intervals h_precond = RPRef.maxCoverageAfterRemovingOne intervals h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (intervals : List (Prod Nat Nat)) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) :
    RPOrig.maxCoverageAfterRemovingOne intervals h_precond = RPRef.maxCoverageAfterRemovingOne intervals h_precond := rfl

theorem rp_equiv_delta_rfl (intervals : List (Prod Nat Nat)) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) :
    RPOrig.maxCoverageAfterRemovingOne intervals h_precond = RPRef.maxCoverageAfterRemovingOne intervals h_precond := by
  delta RPOrig.maxCoverageAfterRemovingOne RPRef.maxCoverageAfterRemovingOne
  rfl

theorem rp_equiv_simp_only (intervals : List (Prod Nat Nat)) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) :
    RPOrig.maxCoverageAfterRemovingOne intervals h_precond = RPRef.maxCoverageAfterRemovingOne intervals h_precond := by
  (simp only [RPOrig.maxCoverageAfterRemovingOne, RPRef.maxCoverageAfterRemovingOne]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxCoverageAfterRemovingOne RPRef.maxCoverageAfterRemovingOne; rfl))

theorem rp_equiv_simp (intervals : List (Prod Nat Nat)) (h_precond : maxCoverageAfterRemovingOne_precond (intervals)) :
    RPOrig.maxCoverageAfterRemovingOne intervals h_precond = RPRef.maxCoverageAfterRemovingOne intervals h_precond := by
  (simp [RPOrig.maxCoverageAfterRemovingOne, RPRef.maxCoverageAfterRemovingOne]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxCoverageAfterRemovingOne RPRef.maxCoverageAfterRemovingOne; rfl))
