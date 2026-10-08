-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def differenceMinMax_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond



namespace RPOrig

def differenceMinMax (a : Array Int) (h_precond : differenceMinMax_precond (a)) : Int :=
  let rec loop (i : Nat) (minVal maxVal : Int) : Int :=
    if i < a.size then
      let x := a[i]!
      let newMin := if x < minVal then x else minVal
      let newMax := if x > maxVal then x else maxVal
      loop (i + 1) newMin newMax
    else
      maxVal - minVal
  loop 1 (a[0]!) (a[0]!)
end RPOrig

namespace RPRef

def differenceMinMax (a : Array Int) (h_precond : differenceMinMax_precond (a)) : Int :=
  let rec loop (i : Nat) (minVal maxVal : Int) : Int :=
    if i < a.size then
      let x := a[i]!
      let newMin := if x < minVal then x else minVal
      let newMax := if x > maxVal then x else maxVal
      loop (1 + i) newMin newMax
    else
      maxVal - minVal
  loop 1 (a[0]!) (a[0]!)
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : differenceMinMax_precond (a)) :
    RPOrig.differenceMinMax a h_precond = RPRef.differenceMinMax a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : differenceMinMax_precond (a)) :
    RPOrig.differenceMinMax a h_precond = RPRef.differenceMinMax a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : differenceMinMax_precond (a)) :
    RPOrig.differenceMinMax a h_precond = RPRef.differenceMinMax a h_precond := by
  delta RPOrig.differenceMinMax RPRef.differenceMinMax RPOrig.differenceMinMax.loop RPRef.differenceMinMax.loop
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : differenceMinMax_precond (a)) :
    RPOrig.differenceMinMax a h_precond = RPRef.differenceMinMax a h_precond := by
  first
    | (simp only [RPOrig.differenceMinMax, RPRef.differenceMinMax, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.differenceMinMax RPRef.differenceMinMax RPOrig.differenceMinMax.loop RPRef.differenceMinMax.loop; rfl))
    | (simp only [RPOrig.differenceMinMax, RPRef.differenceMinMax, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.differenceMinMax RPRef.differenceMinMax RPOrig.differenceMinMax.loop RPRef.differenceMinMax.loop; rfl))
    | (simp only [RPOrig.differenceMinMax, RPRef.differenceMinMax, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.differenceMinMax RPRef.differenceMinMax RPOrig.differenceMinMax.loop RPRef.differenceMinMax.loop; rfl))
    | (simp only [RPOrig.differenceMinMax, RPRef.differenceMinMax]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.differenceMinMax RPRef.differenceMinMax RPOrig.differenceMinMax.loop RPRef.differenceMinMax.loop; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : differenceMinMax_precond (a)) :
    RPOrig.differenceMinMax a h_precond = RPRef.differenceMinMax a h_precond := by
  first
    | (simp [RPOrig.differenceMinMax, RPRef.differenceMinMax, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.differenceMinMax RPRef.differenceMinMax RPOrig.differenceMinMax.loop RPRef.differenceMinMax.loop; rfl))
    | (simp [RPOrig.differenceMinMax, RPRef.differenceMinMax, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.differenceMinMax RPRef.differenceMinMax RPOrig.differenceMinMax.loop RPRef.differenceMinMax.loop; rfl))
    | (simp [RPOrig.differenceMinMax, RPRef.differenceMinMax, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.differenceMinMax RPRef.differenceMinMax RPOrig.differenceMinMax.loop RPRef.differenceMinMax.loop; rfl))
    | (simp [RPOrig.differenceMinMax, RPRef.differenceMinMax]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.differenceMinMax RPRef.differenceMinMax RPOrig.differenceMinMax.loop RPRef.differenceMinMax.loop; rfl))

theorem rp_equiv_ac_rfl (a : Array Int) (h_precond : differenceMinMax_precond (a)) :
    RPOrig.differenceMinMax a h_precond = RPRef.differenceMinMax a h_precond := by
  (try simp only [RPOrig.differenceMinMax, RPRef.differenceMinMax]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.differenceMinMax RPRef.differenceMinMax RPOrig.differenceMinMax.loop RPRef.differenceMinMax.loop; rfl))
