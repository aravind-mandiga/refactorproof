-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def CalSum_precond (N : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def CalSum (N : Nat) (h_precond : CalSum_precond (N)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n = 0 then 0
    else n + loop (n - 1)
  loop N
end RPOrig

namespace RPRef

def CalSum (N : Nat) (h_precond : CalSum_precond (N)) : Nat :=
  let __rp_tmp_4430a640 : Nat :=
    let rec loop (n : Nat) : Nat :=
      if n = 0 then 0
      else n + loop (n - 1)
    loop N
  __rp_tmp_4430a640
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (N : Nat) (h_precond : CalSum_precond (N)) :
    RPOrig.CalSum N h_precond = RPRef.CalSum N h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (N : Nat) (h_precond : CalSum_precond (N)) :
    RPOrig.CalSum N h_precond = RPRef.CalSum N h_precond := rfl

theorem rp_equiv_delta_rfl (N : Nat) (h_precond : CalSum_precond (N)) :
    RPOrig.CalSum N h_precond = RPRef.CalSum N h_precond := by
  delta RPOrig.CalSum RPRef.CalSum RPOrig.CalSum.loop RPRef.CalSum.loop
  rfl

theorem rp_equiv_simp_only (N : Nat) (h_precond : CalSum_precond (N)) :
    RPOrig.CalSum N h_precond = RPRef.CalSum N h_precond := by
  (simp only [RPOrig.CalSum, RPRef.CalSum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.CalSum RPRef.CalSum RPOrig.CalSum.loop RPRef.CalSum.loop; rfl))

theorem rp_equiv_simp (N : Nat) (h_precond : CalSum_precond (N)) :
    RPOrig.CalSum N h_precond = RPRef.CalSum N h_precond := by
  (simp [RPOrig.CalSum, RPRef.CalSum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.CalSum RPRef.CalSum RPOrig.CalSum.loop RPRef.CalSum.loop; rfl))
