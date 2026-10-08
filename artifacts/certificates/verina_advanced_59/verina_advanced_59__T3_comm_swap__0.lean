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

def palindromeIgnoreNonAlnum (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) : Bool :=
  let cleaned : List Char :=
    s.data.filter (fun c => c.isDigit || c.isAlpha)
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
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    RPOrig.palindromeIgnoreNonAlnum s h_precond = RPRef.palindromeIgnoreNonAlnum s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    RPOrig.palindromeIgnoreNonAlnum s h_precond = RPRef.palindromeIgnoreNonAlnum s h_precond := rfl

theorem rp_equiv_delta_rfl (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    RPOrig.palindromeIgnoreNonAlnum s h_precond = RPRef.palindromeIgnoreNonAlnum s h_precond := by
  delta RPOrig.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum RPOrig.palindromeIgnoreNonAlnum.check RPRef.palindromeIgnoreNonAlnum.check
  rfl

theorem rp_equiv_simp_only (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    RPOrig.palindromeIgnoreNonAlnum s h_precond = RPRef.palindromeIgnoreNonAlnum s h_precond := by
  first
    | (simp only [RPOrig.palindromeIgnoreNonAlnum, RPRef.palindromeIgnoreNonAlnum, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum RPOrig.palindromeIgnoreNonAlnum.check RPRef.palindromeIgnoreNonAlnum.check; rfl))
    | (simp only [RPOrig.palindromeIgnoreNonAlnum, RPRef.palindromeIgnoreNonAlnum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum RPOrig.palindromeIgnoreNonAlnum.check RPRef.palindromeIgnoreNonAlnum.check; rfl))
    | (simp only [RPOrig.palindromeIgnoreNonAlnum, RPRef.palindromeIgnoreNonAlnum, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum RPOrig.palindromeIgnoreNonAlnum.check RPRef.palindromeIgnoreNonAlnum.check; rfl))
    | (simp only [RPOrig.palindromeIgnoreNonAlnum, RPRef.palindromeIgnoreNonAlnum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum RPOrig.palindromeIgnoreNonAlnum.check RPRef.palindromeIgnoreNonAlnum.check; rfl))

theorem rp_equiv_simp (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    RPOrig.palindromeIgnoreNonAlnum s h_precond = RPRef.palindromeIgnoreNonAlnum s h_precond := by
  first
    | (simp [RPOrig.palindromeIgnoreNonAlnum, RPRef.palindromeIgnoreNonAlnum, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum RPOrig.palindromeIgnoreNonAlnum.check RPRef.palindromeIgnoreNonAlnum.check; rfl))
    | (simp [RPOrig.palindromeIgnoreNonAlnum, RPRef.palindromeIgnoreNonAlnum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum RPOrig.palindromeIgnoreNonAlnum.check RPRef.palindromeIgnoreNonAlnum.check; rfl))
    | (simp [RPOrig.palindromeIgnoreNonAlnum, RPRef.palindromeIgnoreNonAlnum, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum RPOrig.palindromeIgnoreNonAlnum.check RPRef.palindromeIgnoreNonAlnum.check; rfl))
    | (simp [RPOrig.palindromeIgnoreNonAlnum, RPRef.palindromeIgnoreNonAlnum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum RPOrig.palindromeIgnoreNonAlnum.check RPRef.palindromeIgnoreNonAlnum.check; rfl))

theorem rp_equiv_ac_rfl (s : String) (h_precond : palindromeIgnoreNonAlnum_precond (s)) :
    RPOrig.palindromeIgnoreNonAlnum s h_precond = RPRef.palindromeIgnoreNonAlnum s h_precond := by
  (try simp only [RPOrig.palindromeIgnoreNonAlnum, RPRef.palindromeIgnoreNonAlnum]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.palindromeIgnoreNonAlnum RPRef.palindromeIgnoreNonAlnum RPOrig.palindromeIgnoreNonAlnum.check RPRef.palindromeIgnoreNonAlnum.check; rfl))
