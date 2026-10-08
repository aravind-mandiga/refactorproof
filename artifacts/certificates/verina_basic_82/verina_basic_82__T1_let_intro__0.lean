-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def remove_front_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def copyFrom (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copyFrom a (i + 1) (acc.push (a[i]!))
  else
    acc

namespace RPOrig

def remove_front (a : Array Int) (h_precond : remove_front_precond (a)) : Array Int :=
  if a.size > 0 then
    let c := copyFrom a 1 (Array.mkEmpty (a.size - 1))
    c
  else
    panic "Precondition violation: array is empty"
end RPOrig

namespace RPRef

def remove_front (a : Array Int) (h_precond : remove_front_precond (a)) : Array Int :=
  let __rp_tmp_8b19a12f : Array Int :=
    if a.size > 0 then
      let c := copyFrom a 1 (Array.mkEmpty (a.size - 1))
      c
    else
      panic "Precondition violation: array is empty"
  __rp_tmp_8b19a12f
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : remove_front_precond (a)) :
    RPOrig.remove_front a h_precond = RPRef.remove_front a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : remove_front_precond (a)) :
    RPOrig.remove_front a h_precond = RPRef.remove_front a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : remove_front_precond (a)) :
    RPOrig.remove_front a h_precond = RPRef.remove_front a h_precond := by
  delta RPOrig.remove_front RPRef.remove_front
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : remove_front_precond (a)) :
    RPOrig.remove_front a h_precond = RPRef.remove_front a h_precond := by
  (simp only [RPOrig.remove_front, RPRef.remove_front]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.remove_front RPRef.remove_front; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : remove_front_precond (a)) :
    RPOrig.remove_front a h_precond = RPRef.remove_front a h_precond := by
  (simp [RPOrig.remove_front, RPRef.remove_front]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.remove_front RPRef.remove_front; rfl))
