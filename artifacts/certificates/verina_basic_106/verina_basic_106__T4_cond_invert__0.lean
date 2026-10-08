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
  if ¬ (a.size ≠ b.size) then
    let n := a.size;
    let c := Array.mkArray n 0;
    let rec loop (i : Nat) (c : Array Int) : Array Int :=
      if i < n then
        let c' := c.set! i (a[i]! + b[i]!);
        loop (i + 1) c'
      else c;
    loop 0 c
  else
    panic! "Array lengths mismatch"
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
  first
    | (simp only [RPOrig.arraySum, RPRef.arraySum, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arraySum RPRef.arraySum RPOrig.arraySum.loop RPRef.arraySum.loop; rfl))
    | (simp only [RPOrig.arraySum, RPRef.arraySum, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arraySum RPRef.arraySum RPOrig.arraySum.loop RPRef.arraySum.loop; rfl))
    | (simp only [RPOrig.arraySum, RPRef.arraySum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arraySum RPRef.arraySum RPOrig.arraySum.loop RPRef.arraySum.loop; rfl))

theorem rp_equiv_simp (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) :
    RPOrig.arraySum a b h_precond = RPRef.arraySum a b h_precond := by
  first
    | (simp [RPOrig.arraySum, RPRef.arraySum, ite_not]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arraySum RPRef.arraySum RPOrig.arraySum.loop RPRef.arraySum.loop; rfl))
    | (simp [RPOrig.arraySum, RPRef.arraySum, ite_not, Bool.not_eq_true, decide_not, Nat.not_lt, Nat.not_le, Int.not_lt, Int.not_le]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arraySum RPRef.arraySum RPOrig.arraySum.loop RPRef.arraySum.loop; rfl))
    | (simp [RPOrig.arraySum, RPRef.arraySum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arraySum RPRef.arraySum RPOrig.arraySum.loop RPRef.arraySum.loop; rfl))

theorem rp_equiv_bycases (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) :
    RPOrig.arraySum a b h_precond = RPRef.arraySum a b h_precond := by
  by_cases h : (a.size ≠ b.size) <;> (try simp [h, RPOrig.arraySum, RPRef.arraySum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arraySum RPRef.arraySum RPOrig.arraySum.loop RPRef.arraySum.loop; rfl))

theorem rp_equiv_bycases_ite (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) :
    RPOrig.arraySum a b h_precond = RPRef.arraySum a b h_precond := by
  by_cases h : (a.size ≠ b.size) <;> (try simp [h, ite_not, RPOrig.arraySum, RPRef.arraySum]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arraySum RPRef.arraySum RPOrig.arraySum.loop RPRef.arraySum.loop; rfl))

theorem rp_equiv_split_simp_all (a : Array Int) (b : Array Int) (h_precond : arraySum_precond (a) (b)) :
    RPOrig.arraySum a b h_precond = RPRef.arraySum a b h_precond := by
  simp only [RPOrig.arraySum, RPRef.arraySum]; split <;> (try simp_all) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.arraySum RPRef.arraySum RPOrig.arraySum.loop RPRef.arraySum.loop; rfl))
