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
  let __rp_tmp_eeae87b2 : List Int :=
    let len := l.length
    if len = 0 then l
    else
      (List.range len).map (fun i : Nat =>
        let idx_int : Int := ((Int.ofNat i - Int.ofNat n + Int.ofNat len) % Int.ofNat len)
        let idx_nat : Nat := Int.toNat idx_int
        l.getD idx_nat (l.headD 0)
      )
  __rp_tmp_eeae87b2
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
  (simp only [RPOrig.rotateRight, RPRef.rotateRight]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rotateRight RPRef.rotateRight; rfl))

theorem rp_equiv_simp (l : List Int) (n : Nat) (h_precond : rotateRight_precond (l) (n)) :
    RPOrig.rotateRight l n h_precond = RPRef.rotateRight l n h_precond := by
  (simp [RPOrig.rotateRight, RPRef.rotateRight]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.rotateRight RPRef.rotateRight; rfl))
