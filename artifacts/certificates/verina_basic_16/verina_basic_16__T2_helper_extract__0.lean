-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def replaceChars_precond (s : String) (oldChar : Char) (newChar : Char) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def replaceChars (s : String) (oldChar : Char) (newChar : Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) : String :=
  let cs := s.toList
  let cs' := cs.map (fun c => if c = oldChar then newChar else c)
  String.mk cs'
end RPOrig

namespace RPRef
private def replaceChars__rp_helper_e8782fcd (s : String) (oldChar : Char) (newChar : Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) : String :=
  let cs := s.toList
  let cs' := cs.map (fun c => if c = oldChar then newChar else c)
  String.mk cs'

def replaceChars (s : String) (oldChar : Char) (newChar : Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) : String :=
  replaceChars__rp_helper_e8782fcd s oldChar newChar h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (oldChar : Char) (newChar : Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :
    RPOrig.replaceChars s oldChar newChar h_precond = RPRef.replaceChars s oldChar newChar h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (oldChar : Char) (newChar : Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :
    RPOrig.replaceChars s oldChar newChar h_precond = RPRef.replaceChars s oldChar newChar h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (oldChar : Char) (newChar : Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :
    RPOrig.replaceChars s oldChar newChar h_precond = RPRef.replaceChars s oldChar newChar h_precond := by
  delta RPOrig.replaceChars RPRef.replaceChars RPRef.replaceChars__rp_helper_e8782fcd
  rfl

theorem rp_equiv_simp_only (s : String) (oldChar : Char) (newChar : Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :
    RPOrig.replaceChars s oldChar newChar h_precond = RPRef.replaceChars s oldChar newChar h_precond := by
  (simp only [RPOrig.replaceChars, RPRef.replaceChars, RPRef.replaceChars__rp_helper_e8782fcd]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.replaceChars RPRef.replaceChars RPRef.replaceChars__rp_helper_e8782fcd; rfl))

theorem rp_equiv_simp (s : String) (oldChar : Char) (newChar : Char) (h_precond : replaceChars_precond (s) (oldChar) (newChar)) :
    RPOrig.replaceChars s oldChar newChar h_precond = RPRef.replaceChars s oldChar newChar h_precond := by
  (simp [RPOrig.replaceChars, RPRef.replaceChars, RPRef.replaceChars__rp_helper_e8782fcd]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.replaceChars RPRef.replaceChars RPRef.replaceChars__rp_helper_e8782fcd; rfl))
