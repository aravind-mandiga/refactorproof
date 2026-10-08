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
private def allCharactersSame__rp_helper_3a53cb13 (s : String) (h_precond : allCharactersSame_precond (s)) : Bool :=
  match s.toList with
  | []      => true
  | c :: cs => cs.all (fun x => x = c)

def allCharactersSame (s : String) (h_precond : allCharactersSame_precond (s)) : Bool :=
  allCharactersSame__rp_helper_3a53cb13 s h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : allCharactersSame_precond (s)) :
    RPOrig.allCharactersSame s h_precond = RPRef.allCharactersSame s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : allCharactersSame_precond (s)) :
    RPOrig.allCharactersSame s h_precond = RPRef.allCharactersSame s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : allCharactersSame_precond (s)) :
    RPOrig.allCharactersSame s h_precond = RPRef.allCharactersSame s h_precond := by
  delta RPOrig.allCharactersSame RPRef.allCharactersSame RPRef.allCharactersSame__rp_helper_3a53cb13
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : allCharactersSame_precond (s)) :
    RPOrig.allCharactersSame s h_precond = RPRef.allCharactersSame s h_precond := by
  (simp only [RPOrig.allCharactersSame, RPRef.allCharactersSame, RPRef.allCharactersSame__rp_helper_3a53cb13]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.allCharactersSame RPRef.allCharactersSame RPRef.allCharactersSame__rp_helper_3a53cb13; rfl))

theorem rp_equiv_simp (s : String) (h_precond : allCharactersSame_precond (s)) :
    RPOrig.allCharactersSame s h_precond = RPRef.allCharactersSame s h_precond := by
  (simp [RPOrig.allCharactersSame, RPRef.allCharactersSame, RPRef.allCharactersSame__rp_helper_3a53cb13]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.allCharactersSame RPRef.allCharactersSame RPRef.allCharactersSame__rp_helper_3a53cb13; rfl))
