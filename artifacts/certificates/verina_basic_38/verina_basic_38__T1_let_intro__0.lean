-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def allCharactersSame_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def allCharactersSame (s : String) (h_precond : allCharactersSame_precond (s)) : Bool :=
  match s.toList with
  | []      => true
  | c :: cs => cs.all (fun x => x = c)
end RPOrig

namespace RPRef

def allCharactersSame (s : String) (h_precond : allCharactersSame_precond (s)) : Bool :=
  let __rp_tmp_25b80aff : Bool :=
    match s.toList with
    | []      => true
    | c :: cs => cs.all (fun x => x = c)
  __rp_tmp_25b80aff
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : allCharactersSame_precond (s)) :
    RPOrig.allCharactersSame s h_precond = RPRef.allCharactersSame s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : allCharactersSame_precond (s)) :
    RPOrig.allCharactersSame s h_precond = RPRef.allCharactersSame s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : allCharactersSame_precond (s)) :
    RPOrig.allCharactersSame s h_precond = RPRef.allCharactersSame s h_precond := by
  delta RPOrig.allCharactersSame RPRef.allCharactersSame
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : allCharactersSame_precond (s)) :
    RPOrig.allCharactersSame s h_precond = RPRef.allCharactersSame s h_precond := by
  (simp only [RPOrig.allCharactersSame, RPRef.allCharactersSame]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.allCharactersSame RPRef.allCharactersSame; rfl))

theorem rp_equiv_simp (s : String) (h_precond : allCharactersSame_precond (s)) :
    RPOrig.allCharactersSame s h_precond = RPRef.allCharactersSame s h_precond := by
  (simp [RPOrig.allCharactersSame, RPRef.allCharactersSame]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.allCharactersSame RPRef.allCharactersSame; rfl))
