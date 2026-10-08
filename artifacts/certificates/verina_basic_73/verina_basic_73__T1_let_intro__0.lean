-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Match_precond (s : String) (p : String) : Prop :=
  -- !benchmark @start precond
  s.toList.length = p.toList.length
  -- !benchmark @end precond



namespace RPOrig

def Match (s : String) (p : String) (h_precond : Match_precond (s) (p)) : Bool :=
  let sList := s.toList
  let pList := p.toList
  let rec loop (i : Nat) : Bool :=
    if i < sList.length then
      if (sList[i]! ≠ pList[i]!) ∧ (pList[i]! ≠ '?') then false
      else loop (i + 1)
    else true
  loop 0
end RPOrig

namespace RPRef

def Match (s : String) (p : String) (h_precond : Match_precond (s) (p)) : Bool :=
  let __rp_tmp_59693cf3 : Bool :=
    let sList := s.toList
    let pList := p.toList
    let rec loop (i : Nat) : Bool :=
      if i < sList.length then
        if (sList[i]! ≠ pList[i]!) ∧ (pList[i]! ≠ '?') then false
        else loop (i + 1)
      else true
    loop 0
  __rp_tmp_59693cf3
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (p : String) (h_precond : Match_precond (s) (p)) :
    RPOrig.Match s p h_precond = RPRef.Match s p h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (p : String) (h_precond : Match_precond (s) (p)) :
    RPOrig.Match s p h_precond = RPRef.Match s p h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (p : String) (h_precond : Match_precond (s) (p)) :
    RPOrig.Match s p h_precond = RPRef.Match s p h_precond := by
  delta RPOrig.Match RPRef.Match RPOrig.Match.loop RPRef.Match.loop
  rfl

theorem rp_equiv_simp_only (s : String) (p : String) (h_precond : Match_precond (s) (p)) :
    RPOrig.Match s p h_precond = RPRef.Match s p h_precond := by
  (simp only [RPOrig.Match, RPRef.Match]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Match RPRef.Match RPOrig.Match.loop RPRef.Match.loop; rfl))

theorem rp_equiv_simp (s : String) (p : String) (h_precond : Match_precond (s) (p)) :
    RPOrig.Match s p h_precond = RPRef.Match s p h_precond := by
  (simp [RPOrig.Match, RPRef.Match]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Match RPRef.Match RPOrig.Match.loop RPRef.Match.loop; rfl))
