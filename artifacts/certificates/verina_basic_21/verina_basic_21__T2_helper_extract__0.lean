-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isSublist_precond (sub : List Int) (main : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def isSublist (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) : Bool :=
  let subLen := sub.length
  let mainLen := main.length
  if subLen > mainLen then
    false
  else
    let rec check (i : Nat) : Bool :=
      if i + subLen > mainLen then
        false
      else if sub = (main.drop i).take subLen then
        true
      else if i + 1 ≤ mainLen then
        check (i + 1)
      else
        false
    termination_by mainLen - i
    check 0
end RPOrig

namespace RPRef
private def isSublist__rp_helper_dfffab77 (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) : Bool :=
  let subLen := sub.length
  let mainLen := main.length
  if subLen > mainLen then
    false
  else
    let rec check (i : Nat) : Bool :=
      if i + subLen > mainLen then
        false
      else if sub = (main.drop i).take subLen then
        true
      else if i + 1 ≤ mainLen then
        check (i + 1)
      else
        false
    termination_by mainLen - i
    check 0

def isSublist (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) : Bool :=
  isSublist__rp_helper_dfffab77 sub main h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) :
    RPOrig.isSublist sub main h_precond = RPRef.isSublist sub main h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) :
    RPOrig.isSublist sub main h_precond = RPRef.isSublist sub main h_precond := rfl

theorem rp_equiv_delta_rfl (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) :
    RPOrig.isSublist sub main h_precond = RPRef.isSublist sub main h_precond := by
  delta RPOrig.isSublist RPRef.isSublist RPRef.isSublist__rp_helper_dfffab77 RPOrig.isSublist.check RPRef.isSublist__rp_helper_dfffab77.check
  rfl

theorem rp_equiv_simp_only (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) :
    RPOrig.isSublist sub main h_precond = RPRef.isSublist sub main h_precond := by
  (simp only [RPOrig.isSublist, RPRef.isSublist, RPRef.isSublist__rp_helper_dfffab77]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSublist RPRef.isSublist RPRef.isSublist__rp_helper_dfffab77 RPOrig.isSublist.check RPRef.isSublist__rp_helper_dfffab77.check; rfl))

theorem rp_equiv_simp (sub : List Int) (main : List Int) (h_precond : isSublist_precond (sub) (main)) :
    RPOrig.isSublist sub main h_precond = RPRef.isSublist sub main h_precond := by
  (simp [RPOrig.isSublist, RPRef.isSublist, RPRef.isSublist__rp_helper_dfffab77]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isSublist RPRef.isSublist RPRef.isSublist__rp_helper_dfffab77 RPOrig.isSublist.check RPRef.isSublist__rp_helper_dfffab77.check; rfl))
