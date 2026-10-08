-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isLowerCase (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

def shiftMinus32 (c : Char) : Char :=
  Char.ofNat ((c.toNat - 32) % 128)
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def toUppercase_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def toUppercase (s : String) (h_precond : toUppercase_precond (s)) : String :=
  let cs := s.toList
  let cs' := cs.map (fun c => if isLowerCase c then shiftMinus32 c else c)
  String.mk cs'
end RPOrig

namespace RPRef

def toUppercase (s : String) (h_precond : toUppercase_precond (s)) : String :=
  let __rp_tmp_fdcf2c41 : String :=
    let cs := s.toList
    let cs' := cs.map (fun c => if isLowerCase c then shiftMinus32 c else c)
    String.mk cs'
  __rp_tmp_fdcf2c41
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : toUppercase_precond (s)) :
    RPOrig.toUppercase s h_precond = RPRef.toUppercase s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : toUppercase_precond (s)) :
    RPOrig.toUppercase s h_precond = RPRef.toUppercase s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : toUppercase_precond (s)) :
    RPOrig.toUppercase s h_precond = RPRef.toUppercase s h_precond := by
  delta RPOrig.toUppercase RPRef.toUppercase
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : toUppercase_precond (s)) :
    RPOrig.toUppercase s h_precond = RPRef.toUppercase s h_precond := by
  (simp only [RPOrig.toUppercase, RPRef.toUppercase]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.toUppercase RPRef.toUppercase; rfl))

theorem rp_equiv_simp (s : String) (h_precond : toUppercase_precond (s)) :
    RPOrig.toUppercase s h_precond = RPRef.toUppercase s h_precond := by
  (simp [RPOrig.toUppercase, RPRef.toUppercase]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.toUppercase RPRef.toUppercase; rfl))
