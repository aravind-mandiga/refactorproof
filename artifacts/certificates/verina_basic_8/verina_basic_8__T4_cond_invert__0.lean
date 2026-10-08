-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def myMin_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def myMin (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  if a <= b then a else b
end RPOrig

namespace RPRef

def myMin (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  if ¬ (a <= b) then b
  else a
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) :
    RPOrig.myMin a b h_precond = RPRef.myMin a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) :
    RPOrig.myMin a b h_precond = RPRef.myMin a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) :
    RPOrig.myMin a b h_precond = RPRef.myMin a b h_precond := by
  delta RPOrig.myMin RPRef.myMin
  rfl

theorem rp_equiv_simp_only (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) :
    RPOrig.myMin a b h_precond = RPRef.myMin a b h_precond := by
  first
    | (simp only [RPOrig.myMin, RPRef.myMin, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.myMin RPRef.myMin; rfl))
    | (simp only [RPOrig.myMin, RPRef.myMin, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.myMin RPRef.myMin; rfl))
    | (simp only [RPOrig.myMin, RPRef.myMin]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.myMin RPRef.myMin; rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) :
    RPOrig.myMin a b h_precond = RPRef.myMin a b h_precond := by
  first
    | (simp [RPOrig.myMin, RPRef.myMin, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.myMin RPRef.myMin; rfl))
    | (simp [RPOrig.myMin, RPRef.myMin, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.myMin RPRef.myMin; rfl))
    | (simp [RPOrig.myMin, RPRef.myMin]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.myMin RPRef.myMin; rfl))

theorem rp_equiv_bycases (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) :
    RPOrig.myMin a b h_precond = RPRef.myMin a b h_precond := by
  by_cases h : (a <= b) <;> (try simp [h, RPOrig.myMin, RPRef.myMin]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.myMin RPRef.myMin; rfl))

theorem rp_equiv_bycases_ite (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) :
    RPOrig.myMin a b h_precond = RPRef.myMin a b h_precond := by
  by_cases h : (a <= b) <;> (try simp [h, ite_not, RPOrig.myMin, RPRef.myMin]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.myMin RPRef.myMin; rfl))

theorem rp_equiv_split_simp_all (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) :
    RPOrig.myMin a b h_precond = RPRef.myMin a b h_precond := by
  simp only [RPOrig.myMin, RPRef.myMin]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.myMin RPRef.myMin; rfl))
