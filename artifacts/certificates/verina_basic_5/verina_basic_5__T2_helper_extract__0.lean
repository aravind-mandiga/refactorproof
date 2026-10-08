-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def multiply_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def multiply (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) : Int :=
  a * b
end RPOrig

namespace RPRef
private def multiply__rp_helper_3cc08e31 (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) : Int :=
  a * b

def multiply (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) : Int :=
  multiply__rp_helper_3cc08e31 a b h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) :
    RPOrig.multiply a b h_precond = RPRef.multiply a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) :
    RPOrig.multiply a b h_precond = RPRef.multiply a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) :
    RPOrig.multiply a b h_precond = RPRef.multiply a b h_precond := by
  delta RPOrig.multiply RPRef.multiply RPRef.multiply__rp_helper_3cc08e31
  rfl

theorem rp_equiv_simp_only (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) :
    RPOrig.multiply a b h_precond = RPRef.multiply a b h_precond := by
  (simp only [RPOrig.multiply, RPRef.multiply, RPRef.multiply__rp_helper_3cc08e31]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.multiply RPRef.multiply RPRef.multiply__rp_helper_3cc08e31; rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) :
    RPOrig.multiply a b h_precond = RPRef.multiply a b h_precond := by
  (simp [RPOrig.multiply, RPRef.multiply, RPRef.multiply__rp_helper_3cc08e31]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.multiply RPRef.multiply RPRef.multiply__rp_helper_3cc08e31; rfl))
