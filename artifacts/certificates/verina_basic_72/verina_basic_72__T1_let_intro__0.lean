-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def append_precond (a : Array Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def copy (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copy a (i + 1) (acc.push (a[i]!))
  else
    acc

namespace RPOrig

def append (a : Array Int) (b : Int) (h_precond : append_precond (a) (b)) : Array Int :=
  let c_initial := copy a 0 (Array.empty)
  let c_full := c_initial.push b
  c_full
end RPOrig

namespace RPRef

def append (a : Array Int) (b : Int) (h_precond : append_precond (a) (b)) : Array Int :=
  let __rp_tmp_5c71bf88 : Array Int :=
    let c_initial := copy a 0 (Array.empty)
    let c_full := c_initial.push b
    c_full
  __rp_tmp_5c71bf88
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (b : Int) (h_precond : append_precond (a) (b)) :
    RPOrig.append a b h_precond = RPRef.append a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (b : Int) (h_precond : append_precond (a) (b)) :
    RPOrig.append a b h_precond = RPRef.append a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (b : Int) (h_precond : append_precond (a) (b)) :
    RPOrig.append a b h_precond = RPRef.append a b h_precond := by
  delta RPOrig.append RPRef.append
  rfl

theorem rp_equiv_simp_only (a : Array Int) (b : Int) (h_precond : append_precond (a) (b)) :
    RPOrig.append a b h_precond = RPRef.append a b h_precond := by
  (simp only [RPOrig.append, RPRef.append]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.append RPRef.append; rfl))

theorem rp_equiv_simp (a : Array Int) (b : Int) (h_precond : append_precond (a) (b)) :
    RPOrig.append a b h_precond = RPRef.append a b h_precond := by
  (simp [RPOrig.append, RPRef.append]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.append RPRef.append; rfl))
