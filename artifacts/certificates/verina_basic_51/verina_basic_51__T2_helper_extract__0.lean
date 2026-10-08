-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def BinarySearch_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) a.toList
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def binarySearchLoop (a : Array Int) (key : Int) (lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if (a[mid]! < key) then binarySearchLoop a key (mid + 1) hi
    else binarySearchLoop a key lo mid
  else
    lo

namespace RPOrig

def BinarySearch (a : Array Int) (key : Int) (h_precond : BinarySearch_precond (a) (key)) : Nat :=
  binarySearchLoop a key 0 a.size
end RPOrig

namespace RPRef

private def BinarySearch__rp_helper_486ea936 (a : Array Int) (key : Int) (h_precond : BinarySearch_precond (a) (key)) : Nat :=
  binarySearchLoop a key 0 a.size

def BinarySearch (a : Array Int) (key : Int) (h_precond : BinarySearch_precond (a) (key)) : Nat :=
  BinarySearch__rp_helper_486ea936 a key h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (key : Int) (h_precond : BinarySearch_precond (a) (key)) :
    RPOrig.BinarySearch a key h_precond = RPRef.BinarySearch a key h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (key : Int) (h_precond : BinarySearch_precond (a) (key)) :
    RPOrig.BinarySearch a key h_precond = RPRef.BinarySearch a key h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (key : Int) (h_precond : BinarySearch_precond (a) (key)) :
    RPOrig.BinarySearch a key h_precond = RPRef.BinarySearch a key h_precond := by
  delta RPOrig.BinarySearch RPRef.BinarySearch RPRef.BinarySearch__rp_helper_486ea936
  rfl

theorem rp_equiv_simp_only (a : Array Int) (key : Int) (h_precond : BinarySearch_precond (a) (key)) :
    RPOrig.BinarySearch a key h_precond = RPRef.BinarySearch a key h_precond := by
  (simp only [RPOrig.BinarySearch, RPRef.BinarySearch, RPRef.BinarySearch__rp_helper_486ea936]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.BinarySearch RPRef.BinarySearch RPRef.BinarySearch__rp_helper_486ea936; rfl))

theorem rp_equiv_simp (a : Array Int) (key : Int) (h_precond : BinarySearch_precond (a) (key)) :
    RPOrig.BinarySearch a key h_precond = RPRef.BinarySearch a key h_precond := by
  (simp [RPOrig.BinarySearch, RPRef.BinarySearch, RPRef.BinarySearch__rp_helper_486ea936]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.BinarySearch RPRef.BinarySearch RPRef.BinarySearch__rp_helper_486ea936; rfl))
