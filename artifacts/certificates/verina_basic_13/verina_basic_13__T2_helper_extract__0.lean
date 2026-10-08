-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def cubeElements_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def cubeElements (a : Array Int) (h_precond : cubeElements_precond (a)) : Array Int :=
  a.map (fun x => x * x * x)
end RPOrig

namespace RPRef
private def cubeElements__rp_helper_2cb44842 (a : Array Int) (h_precond : cubeElements_precond (a)) : Array Int :=
  a.map (fun x => x * x * x)

def cubeElements (a : Array Int) (h_precond : cubeElements_precond (a)) : Array Int :=
  cubeElements__rp_helper_2cb44842 a h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : cubeElements_precond (a)) :
    RPOrig.cubeElements a h_precond = RPRef.cubeElements a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : cubeElements_precond (a)) :
    RPOrig.cubeElements a h_precond = RPRef.cubeElements a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : cubeElements_precond (a)) :
    RPOrig.cubeElements a h_precond = RPRef.cubeElements a h_precond := by
  delta RPOrig.cubeElements RPRef.cubeElements RPRef.cubeElements__rp_helper_2cb44842
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : cubeElements_precond (a)) :
    RPOrig.cubeElements a h_precond = RPRef.cubeElements a h_precond := by
  (simp only [RPOrig.cubeElements, RPRef.cubeElements, RPRef.cubeElements__rp_helper_2cb44842]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeElements RPRef.cubeElements RPRef.cubeElements__rp_helper_2cb44842; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : cubeElements_precond (a)) :
    RPOrig.cubeElements a h_precond = RPRef.cubeElements a h_precond := by
  (simp [RPOrig.cubeElements, RPRef.cubeElements, RPRef.cubeElements__rp_helper_2cb44842]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.cubeElements RPRef.cubeElements RPRef.cubeElements__rp_helper_2cb44842; rfl))
