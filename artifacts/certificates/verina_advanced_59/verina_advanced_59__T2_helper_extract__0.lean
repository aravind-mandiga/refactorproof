-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def palindromeIgnoreNonAlnum_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def palindromeIgnoreNonAlnum (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Bool :=
  let cleaned : List Char :=
    s.data.filter (fun c => c.isAlpha || c.isDigit)
      |>.map Char.toLower

  let n := cleaned.length
  let startIndex := 0
  let endIndex := if n = 0 then 0 else n - 1

  let rec check (l r : Nat) : Bool :=
    if l >= r then
      true
    else if cleaned[l]? = cleaned[r]? then
      check (l + 1) (r - 1)
    else
      false

  check startIndex endIndex
end RPOrig

namespace RPRef
private def palindromeIgnoreNonAlnum__rp_helper_737e11e0 (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Bool :=
  let cleaned : List Char :=
    s.data.filter (fun c => c.isAlpha || c.isDigit)
      |>.map Char.toLower

  let n := cleaned.length
  let startIndex := 0
  let endIndex := if n = 0 then 0 else n - 1

  let rec check (l r : Nat) : Bool :=
    if l >= r then
      true
    else if cleaned[l]? = cleaned[r]? then
      check (l + 1) (r - 1)
    else
      false

  check startIndex endIndex

def palindromeIgnoreNonAlnum (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Bool :=
  palindromeIgnoreNonAlnum__rp_helper_737e11e0 s h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    RPOrig.palindromeIgnoreNonAlnum s h_precond = RPRef.palindromeIgnoreNonAlnum s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    RPOrig.palindromeIgnoreNonAlnum s h_precond = RPRef.palindromeIgnoreNonAlnum s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    RPOrig.palindromeIgnoreNonAlnum s h_precond = RPRef.palindromeIgnoreNonAlnum s h_precond := by
  delta RPOrig.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum__rp_helper_737e11e0 RPOrig.palindromeIgnoreNonAlnum.check RPRef.palindromeIgnoreNonAlnum__rp_helper_737e11e0.check
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    RPOrig.palindromeIgnoreNonAlnum s h_precond = RPRef.palindromeIgnoreNonAlnum s h_precond := by
  (simp only [RPOrig.palindromeIgnoreNonAlnum, RPRef.palindromeIgnoreNonAlnum, RPRef.palindromeIgnoreNonAlnum__rp_helper_737e11e0]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum__rp_helper_737e11e0 RPOrig.palindromeIgnoreNonAlnum.check RPRef.palindromeIgnoreNonAlnum__rp_helper_737e11e0.check; rfl))

theorem rp_equiv_simp (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    RPOrig.palindromeIgnoreNonAlnum s h_precond = RPRef.palindromeIgnoreNonAlnum s h_precond := by
  (simp [RPOrig.palindromeIgnoreNonAlnum, RPRef.palindromeIgnoreNonAlnum, RPRef.palindromeIgnoreNonAlnum__rp_helper_737e11e0]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum__rp_helper_737e11e0 RPOrig.palindromeIgnoreNonAlnum.check RPRef.palindromeIgnoreNonAlnum__rp_helper_737e11e0.check; rfl))
