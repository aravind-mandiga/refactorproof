-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isPrime_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n ≥ 2
  -- !benchmark @end precond



namespace RPOrig

def isPrime (n : Nat) (h_precond : isPrime_precond (n)) : Bool :=
  let bound := n
  let rec check (i : Nat) (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i * i > n then true
    else if n % i = 0 then false
    else check (i + 1) (fuel - 1)
  check 2 bound
end RPOrig

namespace RPRef
private def isPrime__rp_helper_99f0df41 (n : Nat) (h_precond : isPrime_precond (n)) : Bool :=
  let bound := n
  let rec check (i : Nat) (fuel : Nat) : Bool :=
    if fuel = 0 then true
    else if i * i > n then true
    else if n % i = 0 then false
    else check (i + 1) (fuel - 1)
  check 2 bound

def isPrime (n : Nat) (h_precond : isPrime_precond (n)) : Bool :=
  isPrime__rp_helper_99f0df41 n h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (h_precond : isPrime_precond (n)) :
    RPOrig.isPrime n h_precond = RPRef.isPrime n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (h_precond : isPrime_precond (n)) :
    RPOrig.isPrime n h_precond = RPRef.isPrime n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (h_precond : isPrime_precond (n)) :
    RPOrig.isPrime n h_precond = RPRef.isPrime n h_precond := by
  delta RPOrig.isPrime RPRef.isPrime RPRef.isPrime__rp_helper_99f0df41 RPOrig.isPrime.check RPRef.isPrime__rp_helper_99f0df41.check
  rfl

theorem rp_equiv_simp_only (n : Nat) (h_precond : isPrime_precond (n)) :
    RPOrig.isPrime n h_precond = RPRef.isPrime n h_precond := by
  (simp only [RPOrig.isPrime, RPRef.isPrime, RPRef.isPrime__rp_helper_99f0df41]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPrime RPRef.isPrime RPRef.isPrime__rp_helper_99f0df41 RPOrig.isPrime.check RPRef.isPrime__rp_helper_99f0df41.check; rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : isPrime_precond (n)) :
    RPOrig.isPrime n h_precond = RPRef.isPrime n h_precond := by
  (simp [RPOrig.isPrime, RPRef.isPrime, RPRef.isPrime__rp_helper_99f0df41]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isPrime RPRef.isPrime RPRef.isPrime__rp_helper_99f0df41 RPOrig.isPrime.check RPRef.isPrime__rp_helper_99f0df41.check; rfl))
