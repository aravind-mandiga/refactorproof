-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isEven (n : Int) : Bool :=
  n % 2 = 0

def isOdd (n : Int) : Bool :=
  n % 2 ≠ 0

def firstEvenOddIndices (lst : List Int) : Option (Nat × Nat) :=
  let evenIndex := lst.findIdx? isEven
  let oddIndex := lst.findIdx? isOdd
  match evenIndex, oddIndex with
  | some ei, some oi => some (ei, oi)
  | _, _ => none
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findProduct_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  lst.length > 1 ∧
  (∃ x ∈ lst, isEven x) ∧
  (∃ x ∈ lst, isOdd x)
  -- !benchmark @end precond



namespace RPOrig

def findProduct (lst : List Int) (h_precond : findProduct_precond (lst)) : Int :=
  match firstEvenOddIndices lst with
  | some (ei, oi) => lst[ei]! * lst[oi]!
  | none => 0
end RPOrig

namespace RPRef

def findProduct (lst : List Int) (h_precond : findProduct_precond (lst)) : Int :=
  let __rp_tmp_1b376f75 : Int :=
    match firstEvenOddIndices lst with
    | some (ei, oi) => lst[ei]! * lst[oi]!
    | none => 0
  __rp_tmp_1b376f75
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (lst : List Int) (h_precond : findProduct_precond (lst)) :
    RPOrig.findProduct lst h_precond = RPRef.findProduct lst h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (lst : List Int) (h_precond : findProduct_precond (lst)) :
    RPOrig.findProduct lst h_precond = RPRef.findProduct lst h_precond := rfl

theorem rp_equiv_delta_rfl (lst : List Int) (h_precond : findProduct_precond (lst)) :
    RPOrig.findProduct lst h_precond = RPRef.findProduct lst h_precond := by
  delta RPOrig.findProduct RPRef.findProduct
  rfl

theorem rp_equiv_simp_only (lst : List Int) (h_precond : findProduct_precond (lst)) :
    RPOrig.findProduct lst h_precond = RPRef.findProduct lst h_precond := by
  (simp only [RPOrig.findProduct, RPRef.findProduct]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findProduct RPRef.findProduct; rfl))

theorem rp_equiv_simp (lst : List Int) (h_precond : findProduct_precond (lst)) :
    RPOrig.findProduct lst h_precond = RPRef.findProduct lst h_precond := by
  (simp [RPOrig.findProduct, RPRef.findProduct]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findProduct RPRef.findProduct; rfl))
