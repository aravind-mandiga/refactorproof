-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Compare_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def Compare (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  if a = b then true else false
end RPOrig

namespace RPRef

def Compare (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  if ¬ (a = b) then false
  else true
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) :
    RPOrig.Compare a b h_precond = RPRef.Compare a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) :
    RPOrig.Compare a b h_precond = RPRef.Compare a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) :
    RPOrig.Compare a b h_precond = RPRef.Compare a b h_precond := by
  delta RPOrig.Compare RPRef.Compare
  rfl

theorem rp_equiv_simp_only (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) :
    RPOrig.Compare a b h_precond = RPRef.Compare a b h_precond := by
  first
    | (simp only [RPOrig.Compare, RPRef.Compare, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Compare RPRef.Compare; rfl))
    | (simp only [RPOrig.Compare, RPRef.Compare, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Compare RPRef.Compare; rfl))
    | (simp only [RPOrig.Compare, RPRef.Compare]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Compare RPRef.Compare; rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) :
    RPOrig.Compare a b h_precond = RPRef.Compare a b h_precond := by
  first
    | (simp [RPOrig.Compare, RPRef.Compare, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Compare RPRef.Compare; rfl))
    | (simp [RPOrig.Compare, RPRef.Compare, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Compare RPRef.Compare; rfl))
    | (simp [RPOrig.Compare, RPRef.Compare]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Compare RPRef.Compare; rfl))

theorem rp_equiv_bycases (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) :
    RPOrig.Compare a b h_precond = RPRef.Compare a b h_precond := by
  by_cases h : (a = b) <;> (try simp [h, RPOrig.Compare, RPRef.Compare]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Compare RPRef.Compare; rfl))

theorem rp_equiv_bycases_ite (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) :
    RPOrig.Compare a b h_precond = RPRef.Compare a b h_precond := by
  by_cases h : (a = b) <;> (try simp [h, ite_not, RPOrig.Compare, RPRef.Compare]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Compare RPRef.Compare; rfl))

theorem rp_equiv_split_simp_all (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) :
    RPOrig.Compare a b h_precond = RPRef.Compare a b h_precond := by
  simp only [RPOrig.Compare, RPRef.Compare]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Compare RPRef.Compare; rfl))
