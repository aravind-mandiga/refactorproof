-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isUpperCase (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

def shift32 (c : Char) : Char :=
  Char.ofNat (c.toNat + 32)
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def toLowercase_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def toLowercase (s : String) (h_precond : toLowercase_precond (s)) : String :=
  let cs := s.toList
  let cs' := cs.map (fun c => if isUpperCase c then shift32 c else c)
  String.mk cs'
end RPOrig

namespace RPRef

def toLowercase (s : String) (h_precond : toLowercase_precond (s)) : String :=
  let __rp_tmp_313f5bc2 : String :=
    let cs := s.toList
    let cs' := cs.map (fun c => if isUpperCase c then shift32 c else c)
    String.mk cs'
  __rp_tmp_313f5bc2
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : toLowercase_precond (s)) :
    RPOrig.toLowercase s h_precond = RPRef.toLowercase s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : toLowercase_precond (s)) :
    RPOrig.toLowercase s h_precond = RPRef.toLowercase s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : toLowercase_precond (s)) :
    RPOrig.toLowercase s h_precond = RPRef.toLowercase s h_precond := by
  delta RPOrig.toLowercase RPRef.toLowercase
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : toLowercase_precond (s)) :
    RPOrig.toLowercase s h_precond = RPRef.toLowercase s h_precond := by
  (simp only [RPOrig.toLowercase, RPRef.toLowercase]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.toLowercase RPRef.toLowercase; rfl))

theorem rp_equiv_simp (s : String) (h_precond : toLowercase_precond (s)) :
    RPOrig.toLowercase s h_precond = RPRef.toLowercase s h_precond := by
  (simp [RPOrig.toLowercase, RPRef.toLowercase]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.toLowercase RPRef.toLowercase; rfl))
