-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def isPowerOfTwo_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def isPowerOfTwo (n : Int) (h_precond : isPowerOfTwo_precond (n)) : Bool :=
  if n <= 0 then false
  else
    let rec aux (m : Int) (fuel : Nat) : Bool :=
      if fuel = 0 then false
      else if m = 1 then true
      else if m % 2 ≠ 0 then false
      else aux (m / 2) (fuel - 1)
    aux n n.natAbs
end RPOrig

namespace RPRef

def isPowerOfTwo (n : Int) (h_precond : isPowerOfTwo_precond (n)) : Bool :=
  if ¬ (n <= 0) then
    let rec aux (m : Int) (fuel : Nat) : Bool :=
      if fuel = 0 then false
      else if m = 1 then true
      else if m % 2 ≠ 0 then false
      else aux (m / 2) (fuel - 1)
    aux n n.natAbs
  else false
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Int) (h_precond : isPowerOfTwo_precond (n)) :
    RPOrig.isPowerOfTwo n h_precond = RPRef.isPowerOfTwo n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Int) (h_precond : isPowerOfTwo_precond (n)) :
    RPOrig.isPowerOfTwo n h_precond = RPRef.isPowerOfTwo n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Int) (h_precond : isPowerOfTwo_precond (n)) :
    RPOrig.isPowerOfTwo n h_precond = RPRef.isPowerOfTwo n h_precond := by
  delta RPOrig.isPowerOfTwo RPRef.isPowerOfTwo RPOrig.isPowerOfTwo.aux RPRef.isPowerOfTwo.aux
  rfl

theorem rp_equiv_simp_only (n : Int) (h_precond : isPowerOfTwo_precond (n)) :
    RPOrig.isPowerOfTwo n h_precond = RPRef.isPowerOfTwo n h_precond := by
  first
    | (simp only [RPOrig.isPowerOfTwo, RPRef.isPowerOfTwo, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPowerOfTwo RPRef.isPowerOfTwo RPOrig.isPowerOfTwo.aux RPRef.isPowerOfTwo.aux; rfl))
    | (simp only [RPOrig.isPowerOfTwo, RPRef.isPowerOfTwo, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPowerOfTwo RPRef.isPowerOfTwo RPOrig.isPowerOfTwo.aux RPRef.isPowerOfTwo.aux; rfl))
    | (simp only [RPOrig.isPowerOfTwo, RPRef.isPowerOfTwo]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPowerOfTwo RPRef.isPowerOfTwo RPOrig.isPowerOfTwo.aux RPRef.isPowerOfTwo.aux; rfl))

theorem rp_equiv_simp (n : Int) (h_precond : isPowerOfTwo_precond (n)) :
    RPOrig.isPowerOfTwo n h_precond = RPRef.isPowerOfTwo n h_precond := by
  first
    | (simp [RPOrig.isPowerOfTwo, RPRef.isPowerOfTwo, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPowerOfTwo RPRef.isPowerOfTwo RPOrig.isPowerOfTwo.aux RPRef.isPowerOfTwo.aux; rfl))
    | (simp [RPOrig.isPowerOfTwo, RPRef.isPowerOfTwo, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPowerOfTwo RPRef.isPowerOfTwo RPOrig.isPowerOfTwo.aux RPRef.isPowerOfTwo.aux; rfl))
    | (simp [RPOrig.isPowerOfTwo, RPRef.isPowerOfTwo]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPowerOfTwo RPRef.isPowerOfTwo RPOrig.isPowerOfTwo.aux RPRef.isPowerOfTwo.aux; rfl))

theorem rp_equiv_bycases (n : Int) (h_precond : isPowerOfTwo_precond (n)) :
    RPOrig.isPowerOfTwo n h_precond = RPRef.isPowerOfTwo n h_precond := by
  by_cases h : (n <= 0) <;> (try simp [h, RPOrig.isPowerOfTwo, RPRef.isPowerOfTwo]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPowerOfTwo RPRef.isPowerOfTwo RPOrig.isPowerOfTwo.aux RPRef.isPowerOfTwo.aux; rfl))

theorem rp_equiv_bycases_ite (n : Int) (h_precond : isPowerOfTwo_precond (n)) :
    RPOrig.isPowerOfTwo n h_precond = RPRef.isPowerOfTwo n h_precond := by
  by_cases h : (n <= 0) <;> (try simp [h, ite_not, RPOrig.isPowerOfTwo, RPRef.isPowerOfTwo]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPowerOfTwo RPRef.isPowerOfTwo RPOrig.isPowerOfTwo.aux RPRef.isPowerOfTwo.aux; rfl))

theorem rp_equiv_split_simp_all (n : Int) (h_precond : isPowerOfTwo_precond (n)) :
    RPOrig.isPowerOfTwo n h_precond = RPRef.isPowerOfTwo n h_precond := by
  simp only [RPOrig.isPowerOfTwo, RPRef.isPowerOfTwo]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPowerOfTwo RPRef.isPowerOfTwo RPOrig.isPowerOfTwo.aux RPRef.isPowerOfTwo.aux; rfl))
