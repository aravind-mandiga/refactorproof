-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isSpaceCommaDot (c : Char) : Bool :=
  if c = ' ' then true
  else if c = ',' then true
  else if c = '.' then true
  else false
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def replaceWithColon_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def replaceWithColon (s : String) (h_precond : replaceWithColon_precond (s)) : String :=
  let cs := s.toList
  let cs' := cs.map (fun c => if isSpaceCommaDot c then ':' else c)
  String.mk cs'
end RPOrig

namespace RPRef
private def replaceWithColon__rp_helper_3e0fbdec (s : String) (h_precond : replaceWithColon_precond (s)) : String :=
  let cs := s.toList
  let cs' := cs.map (fun c => if isSpaceCommaDot c then ':' else c)
  String.mk cs'

def replaceWithColon (s : String) (h_precond : replaceWithColon_precond (s)) : String :=
  replaceWithColon__rp_helper_3e0fbdec s h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : replaceWithColon_precond (s)) :
    RPOrig.replaceWithColon s h_precond = RPRef.replaceWithColon s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : replaceWithColon_precond (s)) :
    RPOrig.replaceWithColon s h_precond = RPRef.replaceWithColon s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : replaceWithColon_precond (s)) :
    RPOrig.replaceWithColon s h_precond = RPRef.replaceWithColon s h_precond := by
  delta RPOrig.replaceWithColon RPRef.replaceWithColon RPRef.replaceWithColon__rp_helper_3e0fbdec
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : replaceWithColon_precond (s)) :
    RPOrig.replaceWithColon s h_precond = RPRef.replaceWithColon s h_precond := by
  (simp only [RPOrig.replaceWithColon, RPRef.replaceWithColon, RPRef.replaceWithColon__rp_helper_3e0fbdec]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.replaceWithColon RPRef.replaceWithColon RPRef.replaceWithColon__rp_helper_3e0fbdec; rfl))

theorem rp_equiv_simp (s : String) (h_precond : replaceWithColon_precond (s)) :
    RPOrig.replaceWithColon s h_precond = RPRef.replaceWithColon s h_precond := by
  (simp [RPOrig.replaceWithColon, RPRef.replaceWithColon, RPRef.replaceWithColon__rp_helper_3e0fbdec]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.replaceWithColon RPRef.replaceWithColon RPRef.replaceWithColon__rp_helper_3e0fbdec; rfl))
