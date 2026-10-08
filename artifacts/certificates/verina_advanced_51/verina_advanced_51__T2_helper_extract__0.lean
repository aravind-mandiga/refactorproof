-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def mergeSorted_precond (a : List Int) (b : List Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) a ∧ List.Pairwise (· ≤ ·) b
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def mergeSortedAux : List Int → List Int → List Int
| [], ys => ys
| xs, [] => xs
| x :: xs', y :: ys' =>
  if x ≤ y then
    let merged := mergeSortedAux xs' (y :: ys')
    x :: merged
  else
    let merged := mergeSortedAux (x :: xs') ys'
    y :: merged


namespace RPOrig

def mergeSorted (a : List Int) (b : List Int) (h_precond : mergeSorted_precond (a) (b)) : List Int :=
  let merged := mergeSortedAux a b
  merged
end RPOrig

namespace RPRef
private def mergeSorted__rp_helper_d7a1c3b5 (a : List Int) (b : List Int) (h_precond : mergeSorted_precond (a) (b)) : List Int :=
  let merged := mergeSortedAux a b
  merged

def mergeSorted (a : List Int) (b : List Int) (h_precond : mergeSorted_precond (a) (b)) : List Int :=
  mergeSorted__rp_helper_d7a1c3b5 a b h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : List Int) (b : List Int) (h_precond : mergeSorted_precond (a) (b)) :
    RPOrig.mergeSorted a b h_precond = RPRef.mergeSorted a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : List Int) (b : List Int) (h_precond : mergeSorted_precond (a) (b)) :
    RPOrig.mergeSorted a b h_precond = RPRef.mergeSorted a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : List Int) (b : List Int) (h_precond : mergeSorted_precond (a) (b)) :
    RPOrig.mergeSorted a b h_precond = RPRef.mergeSorted a b h_precond := by
  delta RPOrig.mergeSorted RPRef.mergeSorted RPRef.mergeSorted__rp_helper_d7a1c3b5
  rfl

theorem rp_equiv_simp_only (a : List Int) (b : List Int) (h_precond : mergeSorted_precond (a) (b)) :
    RPOrig.mergeSorted a b h_precond = RPRef.mergeSorted a b h_precond := by
  (simp only [RPOrig.mergeSorted, RPRef.mergeSorted, RPRef.mergeSorted__rp_helper_d7a1c3b5]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.mergeSorted RPRef.mergeSorted RPRef.mergeSorted__rp_helper_d7a1c3b5; rfl))

theorem rp_equiv_simp (a : List Int) (b : List Int) (h_precond : mergeSorted_precond (a) (b)) :
    RPOrig.mergeSorted a b h_precond = RPRef.mergeSorted a b h_precond := by
  (simp [RPOrig.mergeSorted, RPRef.mergeSorted, RPRef.mergeSorted__rp_helper_d7a1c3b5]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.mergeSorted RPRef.mergeSorted RPRef.mergeSorted__rp_helper_d7a1c3b5; rfl))
