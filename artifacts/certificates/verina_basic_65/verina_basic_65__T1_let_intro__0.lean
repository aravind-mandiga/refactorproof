-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SquareRoot_precond (N : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def SquareRoot (N : Nat) (h_precond : SquareRoot_precond (N)) : Nat :=
  let rec boundedLoop : Nat → Nat → Nat
    | 0, r => r
    | bound+1, r =>
        if (r + 1) * (r + 1) ≤ N then
          boundedLoop bound (r + 1)
        else
          r
  boundedLoop (N+1) 0
end RPOrig

namespace RPRef

def SquareRoot (N : Nat) (h_precond : SquareRoot_precond (N)) : Nat :=
  let __rp_tmp_6d31c4fe : Nat :=
    let rec boundedLoop : Nat → Nat → Nat
      | 0, r => r
      | bound+1, r =>
          if (r + 1) * (r + 1) ≤ N then
            boundedLoop bound (r + 1)
          else
            r
    boundedLoop (N+1) 0
  __rp_tmp_6d31c4fe
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (N : Nat) (h_precond : SquareRoot_precond (N)) :
    RPOrig.SquareRoot N h_precond = RPRef.SquareRoot N h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (N : Nat) (h_precond : SquareRoot_precond (N)) :
    RPOrig.SquareRoot N h_precond = RPRef.SquareRoot N h_precond := rfl

theorem rp_equiv_delta_rfl (N : Nat) (h_precond : SquareRoot_precond (N)) :
    RPOrig.SquareRoot N h_precond = RPRef.SquareRoot N h_precond := by
  delta RPOrig.SquareRoot RPRef.SquareRoot RPOrig.SquareRoot.boundedLoop RPRef.SquareRoot.boundedLoop
  rfl

theorem rp_equiv_simp_only (N : Nat) (h_precond : SquareRoot_precond (N)) :
    RPOrig.SquareRoot N h_precond = RPRef.SquareRoot N h_precond := by
  (simp only [RPOrig.SquareRoot, RPRef.SquareRoot]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SquareRoot RPRef.SquareRoot RPOrig.SquareRoot.boundedLoop RPRef.SquareRoot.boundedLoop; rfl))

theorem rp_equiv_simp (N : Nat) (h_precond : SquareRoot_precond (N)) :
    RPOrig.SquareRoot N h_precond = RPRef.SquareRoot N h_precond := by
  (simp [RPOrig.SquareRoot, RPRef.SquareRoot]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SquareRoot RPRef.SquareRoot RPOrig.SquareRoot.boundedLoop RPRef.SquareRoot.boundedLoop; rfl))
