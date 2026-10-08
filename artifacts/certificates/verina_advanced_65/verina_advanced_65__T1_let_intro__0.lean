-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def reverseString_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def reverseString (s : String) (h_precond : reverseString_precond (s)) : String :=
  let rec reverseAux (chars : List Char) (acc : List Char) : List Char :=
    match chars with
    | [] => acc
    | h::t => reverseAux t (h::acc)
  String.mk (reverseAux (s.toList) [])
end RPOrig

namespace RPRef

def reverseString (s : String) (h_precond : reverseString_precond (s)) : String :=
  let __rp_tmp_96ce5a23 : String :=
    let rec reverseAux (chars : List Char) (acc : List Char) : List Char :=
      match chars with
      | [] => acc
      | h::t => reverseAux t (h::acc)
    String.mk (reverseAux (s.toList) [])
  __rp_tmp_96ce5a23
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : reverseString_precond (s)) :
    RPOrig.reverseString s h_precond = RPRef.reverseString s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : reverseString_precond (s)) :
    RPOrig.reverseString s h_precond = RPRef.reverseString s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : reverseString_precond (s)) :
    RPOrig.reverseString s h_precond = RPRef.reverseString s h_precond := by
  delta RPOrig.reverseString RPRef.reverseString RPOrig.reverseString.reverseAux RPRef.reverseString.reverseAux
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : reverseString_precond (s)) :
    RPOrig.reverseString s h_precond = RPRef.reverseString s h_precond := by
  (simp only [RPOrig.reverseString, RPRef.reverseString]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.reverseString RPRef.reverseString RPOrig.reverseString.reverseAux RPRef.reverseString.reverseAux; rfl))

theorem rp_equiv_simp (s : String) (h_precond : reverseString_precond (s)) :
    RPOrig.reverseString s h_precond = RPRef.reverseString s h_precond := by
  (simp [RPOrig.reverseString, RPRef.reverseString]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.reverseString RPRef.reverseString RPOrig.reverseString.reverseAux RPRef.reverseString.reverseAux; rfl))
