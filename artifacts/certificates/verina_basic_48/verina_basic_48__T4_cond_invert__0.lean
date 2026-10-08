-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isPerfectSquare_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def isPerfectSquare (n : Nat) : Bool :=
  if n = 0 then true
  else
    let rec check (x : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel + 1 =>
        if x * x > n then false
        else if x * x = n then true
        else check (x + 1) fuel
    check 1 n
end RPOrig

namespace RPRef

def isPerfectSquare (n : Nat) : Bool :=
  if ¬ (n = 0) then
    let rec check (x : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | fuel + 1 =>
        if x * x > n then false
        else if x * x = n then true
        else check (x + 1) fuel
    check 1 n
  else true
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := rfl

theorem rp_equiv_delta_rfl (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := by
  delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check
  rfl

theorem rp_equiv_simp_only (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := by
  first
    | (simp only [RPOrig.isPerfectSquare, RPRef.isPerfectSquare, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))
    | (simp only [RPOrig.isPerfectSquare, RPRef.isPerfectSquare, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))
    | (simp only [RPOrig.isPerfectSquare, RPRef.isPerfectSquare]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))

theorem rp_equiv_simp (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := by
  first
    | (simp [RPOrig.isPerfectSquare, RPRef.isPerfectSquare, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))
    | (simp [RPOrig.isPerfectSquare, RPRef.isPerfectSquare, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))
    | (simp [RPOrig.isPerfectSquare, RPRef.isPerfectSquare]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))

theorem rp_equiv_bycases (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := by
  by_cases h : (n = 0) <;> (try simp [h, RPOrig.isPerfectSquare, RPRef.isPerfectSquare]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))

theorem rp_equiv_bycases_ite (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := by
  by_cases h : (n = 0) <;> (try simp [h, ite_not, RPOrig.isPerfectSquare, RPRef.isPerfectSquare]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))

theorem rp_equiv_split_simp_all (n : Nat) :
    RPOrig.isPerfectSquare n = RPRef.isPerfectSquare n := by
  simp only [RPOrig.isPerfectSquare, RPRef.isPerfectSquare]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPerfectSquare RPRef.isPerfectSquare RPOrig.isPerfectSquare.check RPRef.isPerfectSquare.check; rfl))
