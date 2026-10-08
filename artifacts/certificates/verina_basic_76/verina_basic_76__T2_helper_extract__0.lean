-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def myMin_precond (x : Int) (y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def myMin (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) : Int :=
  if x < y then x else y
end RPOrig

namespace RPRef
private def myMin__rp_helper_5e5dcb4d (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) : Int :=
  if x < y then x else y

def myMin (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) : Int :=
  myMin__rp_helper_5e5dcb4d x y h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) :
    RPOrig.myMin x y h_precond = RPRef.myMin x y h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) :
    RPOrig.myMin x y h_precond = RPRef.myMin x y h_precond := rfl

theorem rp_equiv_delta_rfl (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) :
    RPOrig.myMin x y h_precond = RPRef.myMin x y h_precond := by
  delta RPOrig.myMin RPRef.myMin RPRef.myMin__rp_helper_5e5dcb4d
  rfl

theorem rp_equiv_simp_only (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) :
    RPOrig.myMin x y h_precond = RPRef.myMin x y h_precond := by
  (simp only [RPOrig.myMin, RPRef.myMin, RPRef.myMin__rp_helper_5e5dcb4d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.myMin RPRef.myMin RPRef.myMin__rp_helper_5e5dcb4d; rfl))

theorem rp_equiv_simp (x : Int) (y : Int) (h_precond : myMin_precond (x) (y)) :
    RPOrig.myMin x y h_precond = RPRef.myMin x y h_precond := by
  (simp [RPOrig.myMin, RPRef.myMin, RPRef.myMin__rp_helper_5e5dcb4d]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.myMin RPRef.myMin RPRef.myMin__rp_helper_5e5dcb4d; rfl))
