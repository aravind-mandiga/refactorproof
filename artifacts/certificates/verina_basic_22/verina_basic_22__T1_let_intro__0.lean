-- !benchmark @start import type=solution
import Std.Data.HashSet
-- !benchmark @end import

-- !benchmark @start solution_aux
def inArray (a : Array Int) (x : Int) : Bool :=
  a.any (fun y => y = x)
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def dissimilarElements_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def dissimilarElements (a : Array Int) (b : Array Int) (h_precond : dissimilarElements_precond (a) (b)) : Array Int :=
  let res := a.foldl (fun acc x => if !inArray b x then acc.insert x else acc) Std.HashSet.emptyWithCapacity
  let res := b.foldl (fun acc x => if !inArray a x then acc.insert x else acc) res
  (res.toList.mergeSort (· ≤ ·)).toArray
end RPOrig

namespace RPRef

def dissimilarElements (a : Array Int) (b : Array Int) (h_precond : dissimilarElements_precond (a) (b)) : Array Int :=
  let __rp_tmp_bd718fcd : Array Int :=
    let res := a.foldl (fun acc x => if !inArray b x then acc.insert x else acc) Std.HashSet.emptyWithCapacity
    let res := b.foldl (fun acc x => if !inArray a x then acc.insert x else acc) res
    (res.toList.mergeSort (· ≤ ·)).toArray
  __rp_tmp_bd718fcd
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (b : Array Int) (h_precond : dissimilarElements_precond (a) (b)) :
    RPOrig.dissimilarElements a b h_precond = RPRef.dissimilarElements a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (b : Array Int) (h_precond : dissimilarElements_precond (a) (b)) :
    RPOrig.dissimilarElements a b h_precond = RPRef.dissimilarElements a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (b : Array Int) (h_precond : dissimilarElements_precond (a) (b)) :
    RPOrig.dissimilarElements a b h_precond = RPRef.dissimilarElements a b h_precond := by
  delta RPOrig.dissimilarElements RPRef.dissimilarElements
  rfl

theorem rp_equiv_simp_only (a : Array Int) (b : Array Int) (h_precond : dissimilarElements_precond (a) (b)) :
    RPOrig.dissimilarElements a b h_precond = RPRef.dissimilarElements a b h_precond := by
  (simp only [RPOrig.dissimilarElements, RPRef.dissimilarElements]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.dissimilarElements RPRef.dissimilarElements; rfl))

theorem rp_equiv_simp (a : Array Int) (b : Array Int) (h_precond : dissimilarElements_precond (a) (b)) :
    RPOrig.dissimilarElements a b h_precond = RPRef.dissimilarElements a b h_precond := by
  (simp [RPOrig.dissimilarElements, RPRef.dissimilarElements]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.dissimilarElements RPRef.dissimilarElements; rfl))
