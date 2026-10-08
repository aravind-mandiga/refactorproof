-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def maxProfit_precond (prices : List Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def updateMinAndProfit (price : Nat) (minSoFar : Nat) (maxProfit : Nat) : (Nat × Nat) :=
  let newMin := Nat.min minSoFar price
  let profit := if price > minSoFar then price - minSoFar else 0
  let newMaxProfit := Nat.max maxProfit profit
  (newMin, newMaxProfit)

def maxProfitAux (prices : List Nat) (minSoFar : Nat) (maxProfit : Nat) : Nat :=
  match prices with
  | [] => maxProfit
  | p :: ps =>
    let (newMin, newProfit) := updateMinAndProfit p minSoFar maxProfit
    maxProfitAux ps newMin newProfit

namespace RPOrig

def maxProfit (prices : List Nat) (h_precond : maxProfit_precond (prices)) : Nat :=
  match prices with
  | [] => 0
  | p :: ps => maxProfitAux ps p 0
end RPOrig

namespace RPRef

private def maxProfit__rp_helper_0a24c7a3 (prices : List Nat) (h_precond : maxProfit_precond (prices)) : Nat :=
  match prices with
  | [] => 0
  | p :: ps => maxProfitAux ps p 0

def maxProfit (prices : List Nat) (h_precond : maxProfit_precond (prices)) : Nat :=
  maxProfit__rp_helper_0a24c7a3 prices h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (prices : List Nat) (h_precond : maxProfit_precond (prices)) :
    RPOrig.maxProfit prices h_precond = RPRef.maxProfit prices h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (prices : List Nat) (h_precond : maxProfit_precond (prices)) :
    RPOrig.maxProfit prices h_precond = RPRef.maxProfit prices h_precond := rfl

theorem rp_equiv_delta_rfl (prices : List Nat) (h_precond : maxProfit_precond (prices)) :
    RPOrig.maxProfit prices h_precond = RPRef.maxProfit prices h_precond := by
  delta RPOrig.maxProfit RPRef.maxProfit RPRef.maxProfit__rp_helper_0a24c7a3
  rfl

theorem rp_equiv_simp_only (prices : List Nat) (h_precond : maxProfit_precond (prices)) :
    RPOrig.maxProfit prices h_precond = RPRef.maxProfit prices h_precond := by
  (simp only [RPOrig.maxProfit, RPRef.maxProfit, RPRef.maxProfit__rp_helper_0a24c7a3]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxProfit RPRef.maxProfit RPRef.maxProfit__rp_helper_0a24c7a3; rfl))

theorem rp_equiv_simp (prices : List Nat) (h_precond : maxProfit_precond (prices)) :
    RPOrig.maxProfit prices h_precond = RPRef.maxProfit prices h_precond := by
  (simp [RPOrig.maxProfit, RPRef.maxProfit, RPRef.maxProfit__rp_helper_0a24c7a3]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.maxProfit RPRef.maxProfit RPRef.maxProfit__rp_helper_0a24c7a3; rfl))
