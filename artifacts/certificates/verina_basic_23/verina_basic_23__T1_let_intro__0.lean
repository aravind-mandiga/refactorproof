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
  let __rp_tmp_be202508 : Int :=
    let rec loop (i : Nat) (minVal maxVal : Int) : Int :=
      if i < a.size then
        let x := a[i]!
        let newMin := if x < minVal then x else minVal
        let newMax := if x > maxVal then x else maxVal
        loop (i + 1) newMin newMax
      else
        maxVal - minVal
    loop 1 (a[0]!) (a[0]!)
  __rp_tmp_be202508
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
  (simp only [RPOrig.differenceMinMax, RPRef.differenceMinMax]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.differenceMinMax RPRef.differenceMinMax RPOrig.differenceMinMax.loop RPRef.differenceMinMax.loop; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : differenceMinMax_precond (a)) :
    RPOrig.differenceMinMax a h_precond = RPRef.differenceMinMax a h_precond := by
  (simp [RPOrig.differenceMinMax, RPRef.differenceMinMax]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.differenceMinMax RPRef.differenceMinMax RPOrig.differenceMinMax.loop RPRef.differenceMinMax.loop; rfl))
