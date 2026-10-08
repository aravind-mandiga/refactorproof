-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def hasOnlyOneDistinctElement_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond



namespace RPOrig

def hasOnlyOneDistinctElement (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) : Bool :=
  if a.size = 0 then
    true
  else
    let firstElement := a[0]!
    let rec loop (i : Nat) : Bool :=
      if h : i < a.size then
        if a[i]! = firstElement then loop (i + 1) else false
      else
        true
    loop 1
end RPOrig

namespace RPRef

def hasOnlyOneDistinctElement (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) : Bool :=
  let __rp_tmp_eab58287 : Bool :=
    if a.size = 0 then
      true
    else
      let firstElement := a[0]!
      let rec loop (i : Nat) : Bool :=
        if h : i < a.size then
          if a[i]! = firstElement then loop (i + 1) else false
        else
          true
      loop 1
  __rp_tmp_eab58287
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    RPOrig.hasOnlyOneDistinctElement a h_precond = RPRef.hasOnlyOneDistinctElement a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    RPOrig.hasOnlyOneDistinctElement a h_precond = RPRef.hasOnlyOneDistinctElement a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    RPOrig.hasOnlyOneDistinctElement a h_precond = RPRef.hasOnlyOneDistinctElement a h_precond := by
  delta RPOrig.hasOnlyOneDistinctElement RPRef.hasOnlyOneDistinctElement RPOrig.hasOnlyOneDistinctElement.loop RPRef.hasOnlyOneDistinctElement.loop
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    RPOrig.hasOnlyOneDistinctElement a h_precond = RPRef.hasOnlyOneDistinctElement a h_precond := by
  (simp only [RPOrig.hasOnlyOneDistinctElement, RPRef.hasOnlyOneDistinctElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOnlyOneDistinctElement RPRef.hasOnlyOneDistinctElement RPOrig.hasOnlyOneDistinctElement.loop RPRef.hasOnlyOneDistinctElement.loop; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : hasOnlyOneDistinctElement_precond (a)) :
    RPOrig.hasOnlyOneDistinctElement a h_precond = RPRef.hasOnlyOneDistinctElement a h_precond := by
  (simp [RPOrig.hasOnlyOneDistinctElement, RPRef.hasOnlyOneDistinctElement]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasOnlyOneDistinctElement RPRef.hasOnlyOneDistinctElement RPOrig.hasOnlyOneDistinctElement.loop RPRef.hasOnlyOneDistinctElement.loop; rfl))
