-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def kthElement_precond (arr : Array Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k ≥ 1 ∧ k ≤ arr.size
  -- !benchmark @end precond



namespace RPOrig

def kthElement (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) : Int :=
  arr[k - 1]!
end RPOrig

namespace RPRef

def kthElement (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) : Int :=
  let __rp_tmp_3380be52 : Int :=
    arr[k - 1]!
  __rp_tmp_3380be52
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) :
    RPOrig.kthElement arr k h_precond = RPRef.kthElement arr k h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) :
    RPOrig.kthElement arr k h_precond = RPRef.kthElement arr k h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) :
    RPOrig.kthElement arr k h_precond = RPRef.kthElement arr k h_precond := by
  delta RPOrig.kthElement RPRef.kthElement
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) :
    RPOrig.kthElement arr k h_precond = RPRef.kthElement arr k h_precond := by
  (simp only [RPOrig.kthElement, RPRef.kthElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.kthElement RPRef.kthElement; rfl))

theorem rp_equiv_simp (arr : Array Int) (k : Nat) (h_precond : kthElement_precond (arr) (k)) :
    RPOrig.kthElement arr k h_precond = RPRef.kthElement arr k h_precond := by
  (simp [RPOrig.kthElement, RPRef.kthElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.kthElement RPRef.kthElement; rfl))
