-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def myMin_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def myMin (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  if a <= b then a else b
end RPOrig

namespace RPRef
private def myMin__rp_helper_829c4a21 (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  if a <= b then a else b

def myMin (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) : Int :=
  myMin__rp_helper_829c4a21 a b h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) :
    RPOrig.myMin a b h_precond = RPRef.myMin a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) :
    RPOrig.myMin a b h_precond = RPRef.myMin a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) :
    RPOrig.myMin a b h_precond = RPRef.myMin a b h_precond := by
  delta RPOrig.myMin RPRef.myMin RPRef.myMin__rp_helper_829c4a21
  rfl

theorem rp_equiv_simp_only (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) :
    RPOrig.myMin a b h_precond = RPRef.myMin a b h_precond := by
  (simp only [RPOrig.myMin, RPRef.myMin, RPRef.myMin__rp_helper_829c4a21]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.myMin RPRef.myMin RPRef.myMin__rp_helper_829c4a21; rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (h_precond : myMin_precond (a) (b)) :
    RPOrig.myMin a b h_precond = RPRef.myMin a b h_precond := by
  (simp [RPOrig.myMin, RPRef.myMin, RPRef.myMin__rp_helper_829c4a21]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.myMin RPRef.myMin RPRef.myMin__rp_helper_829c4a21; rfl))
