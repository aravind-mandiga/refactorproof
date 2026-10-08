-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def arraySum_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size = b.size
  -- !benchmark @end precond



namespace RPOrig

def arraySum (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) : Array Int :=
  if a.size ≠ b.size then
    panic! "Array lengths mismatch"
  else
    let n := a.size;
    let c := Array.mkArray n 0;
    let rec loop (i : Nat) (c : Array Int) : Array Int :=
      if i < n then
        let c' := c.set! i (a[i]! + b[i]!);
        loop (i + 1) c'
      else c;
    loop 0 c
end RPOrig

namespace RPRef

def arraySum (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) : Array Int :=
  let __rp_tmp_808e270b : Array Int :=
    if a.size ≠ b.size then
      panic! "Array lengths mismatch"
    else
      let n := a.size;
      let c := Array.mkArray n 0;
      let rec loop (i : Nat) (c : Array Int) : Array Int :=
        if i < n then
          let c' := c.set! i (a[i]! + b[i]!);
          loop (i + 1) c'
        else c;
      loop 0 c
  __rp_tmp_808e270b
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) :
    RPOrig.arraySum a b h_precond = RPRef.arraySum a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) :
    RPOrig.arraySum a b h_precond = RPRef.arraySum a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) :
    RPOrig.arraySum a b h_precond = RPRef.arraySum a b h_precond := by
  delta RPOrig.arraySum RPRef.arraySum RPOrig.arraySum.loop RPRef.arraySum.loop
  rfl

theorem rp_equiv_simp_only (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) :
    RPOrig.arraySum a b h_precond = RPRef.arraySum a b h_precond := by
  (simp only [RPOrig.arraySum, RPRef.arraySum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arraySum RPRef.arraySum RPOrig.arraySum.loop RPRef.arraySum.loop; rfl))

theorem rp_equiv_simp (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) :
    RPOrig.arraySum a b h_precond = RPRef.arraySum a b h_precond := by
  (simp [RPOrig.arraySum, RPRef.arraySum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arraySum RPRef.arraySum RPOrig.arraySum.loop RPRef.arraySum.loop; rfl))
