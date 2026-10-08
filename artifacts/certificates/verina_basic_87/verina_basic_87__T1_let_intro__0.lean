-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SelectionSort_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def findMinIndexInRange (arr : Array Int) (start finish : Nat) : Nat :=
  let indices := List.range (finish - start)
  indices.foldl (fun minIdx i =>
    let currIdx := start + i
    if arr[currIdx]! < arr[minIdx]! then currIdx else minIdx
  ) start

def swap (a : Array Int) (i j : Nat) : Array Int :=
  if i < a.size && j < a.size && i ≠ j then
    let temp := a[i]!
    let a' := a.set! i a[j]!
    a'.set! j temp
  else a

namespace RPOrig

def SelectionSort (a : Array Int) (h_precond : SelectionSort_precond (a)) : Array Int :=
  let indices := List.range a.size
  indices.foldl (fun arr i =>
    let minIdx := findMinIndexInRange arr i a.size
    swap arr i minIdx
  ) a
end RPOrig

namespace RPRef

def SelectionSort (a : Array Int) (h_precond : SelectionSort_precond (a)) : Array Int :=
  let __rp_tmp_a3326dad : Array Int :=
    let indices := List.range a.size
    indices.foldl (fun arr i =>
      let minIdx := findMinIndexInRange arr i a.size
      swap arr i minIdx
    ) a
  __rp_tmp_a3326dad
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : SelectionSort_precond (a)) :
    RPOrig.SelectionSort a h_precond = RPRef.SelectionSort a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : SelectionSort_precond (a)) :
    RPOrig.SelectionSort a h_precond = RPRef.SelectionSort a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : SelectionSort_precond (a)) :
    RPOrig.SelectionSort a h_precond = RPRef.SelectionSort a h_precond := by
  delta RPOrig.SelectionSort RPRef.SelectionSort
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : SelectionSort_precond (a)) :
    RPOrig.SelectionSort a h_precond = RPRef.SelectionSort a h_precond := by
  (simp only [RPOrig.SelectionSort, RPRef.SelectionSort]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SelectionSort RPRef.SelectionSort; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : SelectionSort_precond (a)) :
    RPOrig.SelectionSort a h_precond = RPRef.SelectionSort a h_precond := by
  (simp [RPOrig.SelectionSort, RPRef.SelectionSort]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SelectionSort RPRef.SelectionSort; rfl))
