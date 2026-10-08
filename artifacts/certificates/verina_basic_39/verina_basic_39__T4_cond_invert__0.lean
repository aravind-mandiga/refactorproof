-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def rotateRight_precond (l : List Int) (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def rotateRight (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) : List Int :=
  let len := l.length
  if len = 0 then l
  else
    (List.range len).map (fun i : Nat =>
      let idx_int : Int := ((Int.ofNat i - Int.ofNat n + Int.ofNat len) % Int.ofNat len)
      let idx_nat : Nat := Int.toNat idx_int
      l.getD idx_nat (l.headD 0)
    )
end RPOrig

namespace RPRef

def rotateRight (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) : List Int :=
  let len := l.length
  if ¬ (len = 0) then
    (List.range len).map (fun i : Nat =>
      let idx_int : Int := ((Int.ofNat i - Int.ofNat n + Int.ofNat len) % Int.ofNat len)
      let idx_nat : Nat := Int.toNat idx_int
      l.getD idx_nat (l.headD 0)
    )
  else l
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) :
    RPOrig.rotateRight l n h_precond = RPRef.rotateRight l n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) :
    RPOrig.rotateRight l n h_precond = RPRef.rotateRight l n h_precond := rfl

theorem rp_equiv_delta_rfl (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) :
    RPOrig.rotateRight l n h_precond = RPRef.rotateRight l n h_precond := by
  delta RPOrig.rotateRight RPRef.rotateRight
  rfl

theorem rp_equiv_simp_only (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) :
    RPOrig.rotateRight l n h_precond = RPRef.rotateRight l n h_precond := by
  first
    | (simp only [RPOrig.rotateRight, RPRef.rotateRight, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rotateRight RPRef.rotateRight; rfl))
    | (simp only [RPOrig.rotateRight, RPRef.rotateRight, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rotateRight RPRef.rotateRight; rfl))
    | (simp only [RPOrig.rotateRight, RPRef.rotateRight]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rotateRight RPRef.rotateRight; rfl))

theorem rp_equiv_simp (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) :
    RPOrig.rotateRight l n h_precond = RPRef.rotateRight l n h_precond := by
  first
    | (simp [RPOrig.rotateRight, RPRef.rotateRight, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rotateRight RPRef.rotateRight; rfl))
    | (simp [RPOrig.rotateRight, RPRef.rotateRight, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rotateRight RPRef.rotateRight; rfl))
    | (simp [RPOrig.rotateRight, RPRef.rotateRight]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rotateRight RPRef.rotateRight; rfl))

theorem rp_equiv_bycases (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) :
    RPOrig.rotateRight l n h_precond = RPRef.rotateRight l n h_precond := by
  by_cases h : (len = 0) <;> (try simp [h, RPOrig.rotateRight, RPRef.rotateRight]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rotateRight RPRef.rotateRight; rfl))

theorem rp_equiv_bycases_ite (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) :
    RPOrig.rotateRight l n h_precond = RPRef.rotateRight l n h_precond := by
  by_cases h : (len = 0) <;> (try simp [h, ite_not, RPOrig.rotateRight, RPRef.rotateRight]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rotateRight RPRef.rotateRight; rfl))

theorem rp_equiv_split_simp_all (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) :
    RPOrig.rotateRight l n h_precond = RPRef.rotateRight l n h_precond := by
  simp only [RPOrig.rotateRight, RPRef.rotateRight]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rotateRight RPRef.rotateRight; rfl))
