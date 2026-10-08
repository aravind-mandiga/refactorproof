-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def countDigits (n : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else go (n / 10) (acc + 1)
  go n (if n = 0 then 1 else 0)
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def isArmstrong_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def sumPowers (n : Nat) (k : Nat) : Nat :=
  let rec go (n acc : Nat) : Nat :=
    if n = 0 then acc
    else
      let digit := n % 10
      go (n / 10) (acc + digit ^ k)
  go n 0

namespace RPOrig

def isArmstrong (n : Nat) (h_precond : isArmstrong_precond (n)) : Bool :=
  let k := countDigits n
  sumPowers n k = n
end RPOrig

namespace RPRef

def isArmstrong (n : Nat) (h_precond : isArmstrong_precond (n)) : Bool :=
  let __rp_tmp_61ef0a4a : Bool :=
    let k := countDigits n
    sumPowers n k = n
  __rp_tmp_61ef0a4a
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (h_precond : isArmstrong_precond (n)) :
    RPOrig.isArmstrong n h_precond = RPRef.isArmstrong n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (h_precond : isArmstrong_precond (n)) :
    RPOrig.isArmstrong n h_precond = RPRef.isArmstrong n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (h_precond : isArmstrong_precond (n)) :
    RPOrig.isArmstrong n h_precond = RPRef.isArmstrong n h_precond := by
  delta RPOrig.isArmstrong RPRef.isArmstrong
  rfl

theorem rp_equiv_simp_only (n : Nat) (h_precond : isArmstrong_precond (n)) :
    RPOrig.isArmstrong n h_precond = RPRef.isArmstrong n h_precond := by
  (simp only [RPOrig.isArmstrong, RPRef.isArmstrong]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isArmstrong RPRef.isArmstrong; rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : isArmstrong_precond (n)) :
    RPOrig.isArmstrong n h_precond = RPRef.isArmstrong n h_precond := by
  (simp [RPOrig.isArmstrong, RPRef.isArmstrong]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.isArmstrong RPRef.isArmstrong; rfl))
