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
private def reverseString__rp_helper_0d50c7dd (s : String) (h_precond : reverseString_precond (s)) : String :=
  let rec reverseAux (chars : List Char) (acc : List Char) : List Char :=
    match chars with
    | [] => acc
    | h::t => reverseAux t (h::acc)
  String.mk (reverseAux (s.toList) [])

def reverseString (s : String) (h_precond : reverseString_precond (s)) : String :=
  reverseString__rp_helper_0d50c7dd s h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : reverseString_precond (s)) :
    RPOrig.reverseString s h_precond = RPRef.reverseString s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : reverseString_precond (s)) :
    RPOrig.reverseString s h_precond = RPRef.reverseString s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : reverseString_precond (s)) :
    RPOrig.reverseString s h_precond = RPRef.reverseString s h_precond := by
  delta RPOrig.reverseString RPRef.reverseString RPRef.reverseString__rp_helper_0d50c7dd RPOrig.reverseString.reverseAux RPRef.reverseString__rp_helper_0d50c7dd.reverseAux
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : reverseString_precond (s)) :
    RPOrig.reverseString s h_precond = RPRef.reverseString s h_precond := by
  (simp only [RPOrig.reverseString, RPRef.reverseString, RPRef.reverseString__rp_helper_0d50c7dd]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.reverseString RPRef.reverseString RPRef.reverseString__rp_helper_0d50c7dd RPOrig.reverseString.reverseAux RPRef.reverseString__rp_helper_0d50c7dd.reverseAux; rfl))

theorem rp_equiv_simp (s : String) (h_precond : reverseString_precond (s)) :
    RPOrig.reverseString s h_precond = RPRef.reverseString s h_precond := by
  (simp [RPOrig.reverseString, RPRef.reverseString, RPRef.reverseString__rp_helper_0d50c7dd]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.reverseString RPRef.reverseString RPRef.reverseString__rp_helper_0d50c7dd RPOrig.reverseString.reverseAux RPRef.reverseString__rp_helper_0d50c7dd.reverseAux; rfl))
