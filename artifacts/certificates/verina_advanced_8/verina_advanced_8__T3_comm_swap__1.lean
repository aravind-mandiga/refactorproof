-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def canCompleteCircuit_precond (gas : List Int) (cost : List Int) : Prop :=
  -- !benchmark @start precond
  gas.length > 0 ∧ gas.length = cost.length
  -- !benchmark @end precond



namespace RPOrig

def canCompleteCircuit (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) : Int :=
  let totalGas := gas.foldl (· + ·) 0
  let totalCost := cost.foldl (· + ·) 0

  if totalGas < totalCost then
    -1
  else
    let rec loop (g c : List Int) (idx : Nat) (tank : Int) (start : Nat) : Int :=
      match g, c with
      | [], [] => start
      | gi :: gs, ci :: cs =>
        let tank' := tank + gi - ci
        if tank' < 0 then
          loop gs cs (idx + 1) 0 (idx + 1)
        else
          loop gs cs (idx + 1) tank' start
      | _, _ => -1  -- lengths don’t match

    let zipped := List.zip gas cost
    let rec walk (pairs : List (Int × Int)) (i : Nat) (tank : Int) (start : Nat) : Int :=
      match pairs with
      | [] => start
      | (g, c) :: rest =>
        let newTank := tank + g - c
        if newTank < 0 then
          walk rest (i + 1) 0 (i + 1)
        else
          walk rest (i + 1) newTank start

    walk zipped 0 0 0
end RPOrig

namespace RPRef

def canCompleteCircuit (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) : Int :=
  let totalGas := gas.foldl (· + ·) 0
  let totalCost := cost.foldl (· + ·) 0

  if totalGas < totalCost then
    -1
  else
    let rec loop (g c : List Int) (idx : Nat) (tank : Int) (start : Nat) : Int :=
      match g, c with
      | [], [] => start
      | gi :: gs, ci :: cs =>
        let tank' := tank + gi - ci
        if tank' < 0 then
          loop gs cs (1 + idx) 0 (idx + 1)
        else
          loop gs cs (idx + 1) tank' start
      | _, _ => -1  -- lengths don’t match

    let zipped := List.zip gas cost
    let rec walk (pairs : List (Int × Int)) (i : Nat) (tank : Int) (start : Nat) : Int :=
      match pairs with
      | [] => start
      | (g, c) :: rest =>
        let newTank := tank + g - c
        if newTank < 0 then
          walk rest (i + 1) 0 (i + 1)
        else
          walk rest (i + 1) newTank start

    walk zipped 0 0 0
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) :
    RPOrig.canCompleteCircuit gas cost h_precond = RPRef.canCompleteCircuit gas cost h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) :
    RPOrig.canCompleteCircuit gas cost h_precond = RPRef.canCompleteCircuit gas cost h_precond := rfl

theorem rp_equiv_delta_rfl (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) :
    RPOrig.canCompleteCircuit gas cost h_precond = RPRef.canCompleteCircuit gas cost h_precond := by
  delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk
  rfl

theorem rp_equiv_simp_only (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) :
    RPOrig.canCompleteCircuit gas cost h_precond = RPRef.canCompleteCircuit gas cost h_precond := by
  first
    | (simp only [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))
    | (simp only [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))
    | (simp only [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))
    | (simp only [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))

theorem rp_equiv_simp (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) :
    RPOrig.canCompleteCircuit gas cost h_precond = RPRef.canCompleteCircuit gas cost h_precond := by
  first
    | (simp [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))
    | (simp [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))
    | (simp [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))
    | (simp [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))

theorem rp_equiv_ac_rfl (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) :
    RPOrig.canCompleteCircuit gas cost h_precond = RPRef.canCompleteCircuit gas cost h_precond := by
  (try simp only [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))
