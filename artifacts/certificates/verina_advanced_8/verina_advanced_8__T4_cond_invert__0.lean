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

  if ¬ (totalGas < totalCost) then
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
  else
    -1
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
    | (simp only [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))
    | (simp only [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))
    | (simp only [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))

theorem rp_equiv_simp (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) :
    RPOrig.canCompleteCircuit gas cost h_precond = RPRef.canCompleteCircuit gas cost h_precond := by
  first
    | (simp [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))
    | (simp [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))
    | (simp [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))

theorem rp_equiv_bycases (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) :
    RPOrig.canCompleteCircuit gas cost h_precond = RPRef.canCompleteCircuit gas cost h_precond := by
  by_cases h : (totalGas < totalCost) <;> (try simp [h, RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))

theorem rp_equiv_bycases_ite (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) :
    RPOrig.canCompleteCircuit gas cost h_precond = RPRef.canCompleteCircuit gas cost h_precond := by
  by_cases h : (totalGas < totalCost) <;> (try simp [h, ite_not, RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))

theorem rp_equiv_split_simp_all (gas : List Int) (cost : List Int) (h_precond : canCompleteCircuit_precond (gas) (cost)) :
    RPOrig.canCompleteCircuit gas cost h_precond = RPRef.canCompleteCircuit gas cost h_precond := by
  simp only [RPOrig.canCompleteCircuit, RPRef.canCompleteCircuit]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.canCompleteCircuit RPRef.canCompleteCircuit RPOrig.canCompleteCircuit.loop RPOrig.canCompleteCircuit.walk RPRef.canCompleteCircuit.loop RPRef.canCompleteCircuit.walk; rfl))
