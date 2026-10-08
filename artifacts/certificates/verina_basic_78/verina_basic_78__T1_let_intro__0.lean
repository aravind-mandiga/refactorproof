-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def MultipleReturns_precond (x : Int) (y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def MultipleReturns (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) : (Int × Int) :=
  let more := x + y
  let less := x - y
  (more, less)
end RPOrig

namespace RPRef

def MultipleReturns (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) : (Int × Int) :=
  let __rp_tmp_ce491c75 : (Int × Int) :=
    let more := x + y
    let less := x - y
    (more, less)
  __rp_tmp_ce491c75
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) :
    RPOrig.MultipleReturns x y h_precond = RPRef.MultipleReturns x y h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) :
    RPOrig.MultipleReturns x y h_precond = RPRef.MultipleReturns x y h_precond := rfl

theorem rp_equiv_delta_rfl (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) :
    RPOrig.MultipleReturns x y h_precond = RPRef.MultipleReturns x y h_precond := by
  delta RPOrig.MultipleReturns RPRef.MultipleReturns
  rfl

theorem rp_equiv_simp_only (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) :
    RPOrig.MultipleReturns x y h_precond = RPRef.MultipleReturns x y h_precond := by
  (simp only [RPOrig.MultipleReturns, RPRef.MultipleReturns]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.MultipleReturns RPRef.MultipleReturns; rfl))

theorem rp_equiv_simp (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) :
    RPOrig.MultipleReturns x y h_precond = RPRef.MultipleReturns x y h_precond := by
  (simp [RPOrig.MultipleReturns, RPRef.MultipleReturns]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.MultipleReturns RPRef.MultipleReturns; rfl))
