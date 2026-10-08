-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def secondSmallest_precond (s : Array Int) : Prop :=
  -- !benchmark @start precond
  s.size > 1 ∧ ∃ i j, i < s.size ∧ j < s.size ∧ s[i]! ≠ s[j]!  -- at least two distinct values
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def secondSmallestAux (s : Array Int) (i minIdx : Nat) (secondIdx : Option Nat) : Int :=
  if i ≥ s.size then
    match secondIdx with
    | some si => s[si]!
    | none => panic! "no second smallest"  -- unreachable given precondition
  else
    let x := s[i]!
    let m := s[minIdx]!
    match secondIdx with
    | none =>
      if x < m then
        secondSmallestAux s (i + 1) i (some minIdx)
      else if x > m then
        secondSmallestAux s (i + 1) minIdx (some i)
      else
        secondSmallestAux s (i + 1) minIdx none
    | some si =>
      let smin := s[si]!
      if x < m then
        secondSmallestAux s (i + 1) i (some minIdx)
      else if x < smin ∧ x > m then
        secondSmallestAux s (i + 1) minIdx (some i)
      else
        secondSmallestAux s (i + 1) minIdx (some si)
termination_by s.size - i

namespace RPOrig

def secondSmallest (s : Array Int) (h_precond : secondSmallest_precond (s)) : Int :=
  secondSmallestAux s 1 0 none
end RPOrig

namespace RPRef

private def secondSmallest__rp_helper_73d614f2 (s : Array Int) (h_precond : secondSmallest_precond (s)) : Int :=
  secondSmallestAux s 1 0 none

def secondSmallest (s : Array Int) (h_precond : secondSmallest_precond (s)) : Int :=
  secondSmallest__rp_helper_73d614f2 s h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (s : Array Int) (h_precond : secondSmallest_precond (s)) :
    RPOrig.secondSmallest s h_precond = RPRef.secondSmallest s h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (s : Array Int) (h_precond : secondSmallest_precond (s)) :
    RPOrig.secondSmallest s h_precond = RPRef.secondSmallest s h_precond := rfl

theorem rp_equiv_delta_rfl (s : Array Int) (h_precond : secondSmallest_precond (s)) :
    RPOrig.secondSmallest s h_precond = RPRef.secondSmallest s h_precond := by
  delta RPOrig.secondSmallest RPRef.secondSmallest RPRef.secondSmallest__rp_helper_73d614f2
  rfl

theorem rp_equiv_simp_only (s : Array Int) (h_precond : secondSmallest_precond (s)) :
    RPOrig.secondSmallest s h_precond = RPRef.secondSmallest s h_precond := by
  (simp only [RPOrig.secondSmallest, RPRef.secondSmallest, RPRef.secondSmallest__rp_helper_73d614f2]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.secondSmallest RPRef.secondSmallest RPRef.secondSmallest__rp_helper_73d614f2; rfl))

theorem rp_equiv_simp (s : Array Int) (h_precond : secondSmallest_precond (s)) :
    RPOrig.secondSmallest s h_precond = RPRef.secondSmallest s h_precond := by
  (simp [RPOrig.secondSmallest, RPRef.secondSmallest, RPRef.secondSmallest__rp_helper_73d614f2]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.secondSmallest RPRef.secondSmallest RPRef.secondSmallest__rp_helper_73d614f2; rfl))
