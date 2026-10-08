-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isDigit (c : Char) : Bool :=
  (c ≥ '0') && (c ≤ '9')
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def allDigits_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def allDigits (s : String) (h_precond : allDigits_precond (s)) : Bool :=
  let rec loop (it : String.Iterator) : Bool :=
    if it.atEnd then
      true
    else
      if !isDigit it.curr then
        false
      else
        loop it.next
  loop s.iter
end RPOrig

namespace RPRef
private def allDigits__rp_helper_2417dd8f (s : String) (h_precond : allDigits_precond (s)) : Bool :=
  let rec loop (it : String.Iterator) : Bool :=
    if it.atEnd then
      true
    else
      if !isDigit it.curr then
        false
      else
        loop it.next
  loop s.iter

def allDigits (s : String) (h_precond : allDigits_precond (s)) : Bool :=
  allDigits__rp_helper_2417dd8f s h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : allDigits_precond (s)) :
    RPOrig.allDigits s h_precond = RPRef.allDigits s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : allDigits_precond (s)) :
    RPOrig.allDigits s h_precond = RPRef.allDigits s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : allDigits_precond (s)) :
    RPOrig.allDigits s h_precond = RPRef.allDigits s h_precond := by
  delta RPOrig.allDigits RPRef.allDigits RPRef.allDigits__rp_helper_2417dd8f RPOrig.allDigits.loop RPRef.allDigits__rp_helper_2417dd8f.loop
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : allDigits_precond (s)) :
    RPOrig.allDigits s h_precond = RPRef.allDigits s h_precond := by
  (simp only [RPOrig.allDigits, RPRef.allDigits, RPRef.allDigits__rp_helper_2417dd8f]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.allDigits RPRef.allDigits RPRef.allDigits__rp_helper_2417dd8f RPOrig.allDigits.loop RPRef.allDigits__rp_helper_2417dd8f.loop; rfl))

theorem rp_equiv_simp (s : String) (h_precond : allDigits_precond (s)) :
    RPOrig.allDigits s h_precond = RPRef.allDigits s h_precond := by
  (simp [RPOrig.allDigits, RPRef.allDigits, RPRef.allDigits__rp_helper_2417dd8f]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.allDigits RPRef.allDigits RPRef.allDigits__rp_helper_2417dd8f RPOrig.allDigits.loop RPRef.allDigits__rp_helper_2417dd8f.loop; rfl))
