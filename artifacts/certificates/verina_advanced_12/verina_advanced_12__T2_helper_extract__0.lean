-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def firstDuplicate_precond (lst : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def firstDuplicate (lst : List Int) (h_precond : firstDuplicate_precond (lst)) : Option Int :=
  let rec helper (seen : List Int) (rem : List Int) : Option Int :=
    match rem with
    | [] => none
    | h :: t => if seen.contains h then some h else helper (h :: seen) t
  helper [] lst
end RPOrig

namespace RPRef
private def firstDuplicate__rp_helper_69f1430c (lst : List Int) (h_precond : firstDuplicate_precond (lst)) : Option Int :=
  let rec helper (seen : List Int) (rem : List Int) : Option Int :=
    match rem with
    | [] => none
    | h :: t => if seen.contains h then some h else helper (h :: seen) t
  helper [] lst

def firstDuplicate (lst : List Int) (h_precond : firstDuplicate_precond (lst)) : Option Int :=
  firstDuplicate__rp_helper_69f1430c lst h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (lst : List Int) (h_precond : firstDuplicate_precond (lst)) :
    RPOrig.firstDuplicate lst h_precond = RPRef.firstDuplicate lst h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (lst : List Int) (h_precond : firstDuplicate_precond (lst)) :
    RPOrig.firstDuplicate lst h_precond = RPRef.firstDuplicate lst h_precond := rfl

theorem rp_equiv_delta_rfl (lst : List Int) (h_precond : firstDuplicate_precond (lst)) :
    RPOrig.firstDuplicate lst h_precond = RPRef.firstDuplicate lst h_precond := by
  delta RPOrig.firstDuplicate RPRef.firstDuplicate RPRef.firstDuplicate__rp_helper_69f1430c RPOrig.firstDuplicate.helper RPRef.firstDuplicate__rp_helper_69f1430c.helper
  rfl

theorem rp_equiv_simp_only (lst : List Int) (h_precond : firstDuplicate_precond (lst)) :
    RPOrig.firstDuplicate lst h_precond = RPRef.firstDuplicate lst h_precond := by
  (simp only [RPOrig.firstDuplicate, RPRef.firstDuplicate, RPRef.firstDuplicate__rp_helper_69f1430c]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.firstDuplicate RPRef.firstDuplicate RPRef.firstDuplicate__rp_helper_69f1430c RPOrig.firstDuplicate.helper RPRef.firstDuplicate__rp_helper_69f1430c.helper; rfl))

theorem rp_equiv_simp (lst : List Int) (h_precond : firstDuplicate_precond (lst)) :
    RPOrig.firstDuplicate lst h_precond = RPRef.firstDuplicate lst h_precond := by
  (simp [RPOrig.firstDuplicate, RPRef.firstDuplicate, RPRef.firstDuplicate__rp_helper_69f1430c]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.firstDuplicate RPRef.firstDuplicate RPRef.firstDuplicate__rp_helper_69f1430c RPOrig.firstDuplicate.helper RPRef.firstDuplicate__rp_helper_69f1430c.helper; rfl))
