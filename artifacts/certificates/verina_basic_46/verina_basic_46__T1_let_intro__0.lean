-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def lastPosition_precond (arr : Array Int) (elem : Int) : Prop :=
  -- !benchmark @start precond
  List.Pairwise (· ≤ ·) arr.toList
  -- !benchmark @end precond



namespace RPOrig

def lastPosition (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) : Int :=
  let rec loop (i : Nat) (pos : Int) : Int :=
    if i < arr.size then
      let a := arr[i]!
      if a = elem then loop (i + 1) i
      else loop (i + 1) pos
    else pos
  loop 0 (-1)
end RPOrig

namespace RPRef

def lastPosition (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) : Int :=
  let __rp_tmp_c9a57c87 : Int :=
    let rec loop (i : Nat) (pos : Int) : Int :=
      if i < arr.size then
        let a := arr[i]!
        if a = elem then loop (i + 1) i
        else loop (i + 1) pos
      else pos
    loop 0 (-1)
  __rp_tmp_c9a57c87
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) :
    RPOrig.lastPosition arr elem h_precond = RPRef.lastPosition arr elem h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) :
    RPOrig.lastPosition arr elem h_precond = RPRef.lastPosition arr elem h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) :
    RPOrig.lastPosition arr elem h_precond = RPRef.lastPosition arr elem h_precond := by
  delta RPOrig.lastPosition RPRef.lastPosition RPOrig.lastPosition.loop RPRef.lastPosition.loop
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) :
    RPOrig.lastPosition arr elem h_precond = RPRef.lastPosition arr elem h_precond := by
  (simp only [RPOrig.lastPosition, RPRef.lastPosition]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lastPosition RPRef.lastPosition RPOrig.lastPosition.loop RPRef.lastPosition.loop; rfl))

theorem rp_equiv_simp (arr : Array Int) (elem : Int) (h_precond : lastPosition_precond (arr) (elem)) :
    RPOrig.lastPosition arr elem h_precond = RPRef.lastPosition arr elem h_precond := by
  (simp [RPOrig.lastPosition, RPRef.lastPosition]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.lastPosition RPRef.lastPosition RPOrig.lastPosition.loop RPRef.lastPosition.loop; rfl))
