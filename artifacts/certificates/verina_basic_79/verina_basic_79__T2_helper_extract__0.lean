-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def onlineMax_precond (a : Array Int) (x : Nat) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧ x > 0 ∧ x < a.size  -- x must be at least 1 (as stated in description)
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def findBest (a : Array Int) (x : Nat) (i : Nat) (best : Int) : Int :=
  if i < x then
    let newBest := if a[i]! > best then a[i]! else best
    findBest a x (i + 1) newBest
  else best

def findP (a : Array Int) (x : Nat) (m : Int) (i : Nat) : Nat :=
  if i < a.size then
    if a[i]! > m then i else findP a x m (i + 1)
  else a.size - 1

namespace RPOrig

def onlineMax (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) : Int × Nat :=
  let best := a[0]!
  let m := findBest a x 1 best;
  let p := findP a x m x;
  (m, p)
end RPOrig

namespace RPRef

private def onlineMax__rp_helper_0ff6a643 (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) : Int × Nat :=
  let best := a[0]!
  let m := findBest a x 1 best;
  let p := findP a x m x;
  (m, p)

def onlineMax (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) : Int × Nat :=
  onlineMax__rp_helper_0ff6a643 a x h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) :
    RPOrig.onlineMax a x h_precond = RPRef.onlineMax a x h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) :
    RPOrig.onlineMax a x h_precond = RPRef.onlineMax a x h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) :
    RPOrig.onlineMax a x h_precond = RPRef.onlineMax a x h_precond := by
  delta RPOrig.onlineMax RPRef.onlineMax RPRef.onlineMax__rp_helper_0ff6a643
  rfl

theorem rp_equiv_simp_only (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) :
    RPOrig.onlineMax a x h_precond = RPRef.onlineMax a x h_precond := by
  (simp only [RPOrig.onlineMax, RPRef.onlineMax, RPRef.onlineMax__rp_helper_0ff6a643]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.onlineMax RPRef.onlineMax RPRef.onlineMax__rp_helper_0ff6a643; rfl))

theorem rp_equiv_simp (a : Array Int) (x : Nat) (h_precond : onlineMax_precond (a) (x)) :
    RPOrig.onlineMax a x h_precond = RPRef.onlineMax a x h_precond := by
  (simp [RPOrig.onlineMax, RPRef.onlineMax, RPRef.onlineMax__rp_helper_0ff6a643]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.onlineMax RPRef.onlineMax RPRef.onlineMax__rp_helper_0ff6a643; rfl))
