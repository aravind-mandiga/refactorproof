-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def findMajorityElement_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def countOccurrences (n : Int) (lst : List Int) : Nat :=
  lst.foldl (fun acc x => if x = n then acc + 1 else acc) 0

namespace RPOrig

def findMajorityElement (lst : List Int) (h_precond : findMajorityElement_precond (lst)) : Int :=
  let n := lst.length
  let majority := lst.find? (fun x => countOccurrences x lst > n / 2)
  match majority with
  | some x => x
  | none => -1
end RPOrig

namespace RPRef

def findMajorityElement (lst : List Int) (h_precond : findMajorityElement_precond (lst)) : Int :=
  let __rp_tmp_da7a0434 : Int :=
    let n := lst.length
    let majority := lst.find? (fun x => countOccurrences x lst > n / 2)
    match majority with
    | some x => x
    | none => -1
  __rp_tmp_da7a0434
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (lst : List Int) (h_precond : findMajorityElement_precond (lst)) :
    RPOrig.findMajorityElement lst h_precond = RPRef.findMajorityElement lst h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (lst : List Int) (h_precond : findMajorityElement_precond (lst)) :
    RPOrig.findMajorityElement lst h_precond = RPRef.findMajorityElement lst h_precond := rfl

theorem rp_equiv_delta_rfl (lst : List Int) (h_precond : findMajorityElement_precond (lst)) :
    RPOrig.findMajorityElement lst h_precond = RPRef.findMajorityElement lst h_precond := by
  delta RPOrig.findMajorityElement RPRef.findMajorityElement
  rfl

theorem rp_equiv_simp_only (lst : List Int) (h_precond : findMajorityElement_precond (lst)) :
    RPOrig.findMajorityElement lst h_precond = RPRef.findMajorityElement lst h_precond := by
  (simp only [RPOrig.findMajorityElement, RPRef.findMajorityElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findMajorityElement RPRef.findMajorityElement; rfl))

theorem rp_equiv_simp (lst : List Int) (h_precond : findMajorityElement_precond (lst)) :
    RPOrig.findMajorityElement lst h_precond = RPRef.findMajorityElement lst h_precond := by
  (simp [RPOrig.findMajorityElement, RPRef.findMajorityElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findMajorityElement RPRef.findMajorityElement; rfl))
