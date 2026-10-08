-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def elementWiseModulo_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size = b.size ∧ a.size > 0 ∧
  (∀ i, i < b.size → b[i]! ≠ 0)
  -- !benchmark @end precond



namespace RPOrig

def elementWiseModulo (a : Array Int) (b : Array Int) (h_precond : elementWiseModulo_precond (a) (b)) : Array Int :=
  a.mapIdx (fun i x => x % b[i]!)
end RPOrig

namespace RPRef

def elementWiseModulo (a : Array Int) (b : Array Int) (h_precond : elementWiseModulo_precond (a) (b)) : Array Int :=
  let __rp_tmp_48be27a6 : Array Int :=
    a.mapIdx (fun i x => x % b[i]!)
  __rp_tmp_48be27a6
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (b : Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :
    RPOrig.elementWiseModulo a b h_precond = RPRef.elementWiseModulo a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (b : Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :
    RPOrig.elementWiseModulo a b h_precond = RPRef.elementWiseModulo a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (b : Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :
    RPOrig.elementWiseModulo a b h_precond = RPRef.elementWiseModulo a b h_precond := by
  delta RPOrig.elementWiseModulo RPRef.elementWiseModulo
  rfl

theorem rp_equiv_simp_only (a : Array Int) (b : Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :
    RPOrig.elementWiseModulo a b h_precond = RPRef.elementWiseModulo a b h_precond := by
  (simp only [RPOrig.elementWiseModulo, RPRef.elementWiseModulo]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.elementWiseModulo RPRef.elementWiseModulo; rfl))

theorem rp_equiv_simp (a : Array Int) (b : Array Int) (h_precond : elementWiseModulo_precond (a) (b)) :
    RPOrig.elementWiseModulo a b h_precond = RPRef.elementWiseModulo a b h_precond := by
  (simp [RPOrig.elementWiseModulo, RPRef.elementWiseModulo]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.elementWiseModulo RPRef.elementWiseModulo; rfl))
