-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def concat_precond (a : Array Int) (b : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def concat (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) : Array Int :=
  let n := a.size + b.size
  let rec loop (i : Nat) (c : Array Int) : Array Int :=
    if i < n then
      let value := if i < a.size then a[i]! else b[i - a.size]!
      loop (i + 1) (c.set! i value)
    else
      c
  loop 0 (Array.mkArray n 0)
end RPOrig

namespace RPRef
private def concat__rp_helper_79736bdc (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) : Array Int :=
  let n := a.size + b.size
  let rec loop (i : Nat) (c : Array Int) : Array Int :=
    if i < n then
      let value := if i < a.size then a[i]! else b[i - a.size]!
      loop (i + 1) (c.set! i value)
    else
      c
  loop 0 (Array.mkArray n 0)

def concat (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) : Array Int :=
  concat__rp_helper_79736bdc a b h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) :
    RPOrig.concat a b h_precond = RPRef.concat a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) :
    RPOrig.concat a b h_precond = RPRef.concat a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) :
    RPOrig.concat a b h_precond = RPRef.concat a b h_precond := by
  delta RPOrig.concat RPRef.concat RPRef.concat__rp_helper_79736bdc RPOrig.concat.loop RPRef.concat__rp_helper_79736bdc.loop
  rfl

theorem rp_equiv_simp_only (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) :
    RPOrig.concat a b h_precond = RPRef.concat a b h_precond := by
  (simp only [RPOrig.concat, RPRef.concat, RPRef.concat__rp_helper_79736bdc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.concat RPRef.concat RPRef.concat__rp_helper_79736bdc RPOrig.concat.loop RPRef.concat__rp_helper_79736bdc.loop; rfl))

theorem rp_equiv_simp (a : Array Int) (b : Array Int) (h_precond : concat_precond (a) (b)) :
    RPOrig.concat a b h_precond = RPRef.concat a b h_precond := by
  (simp [RPOrig.concat, RPRef.concat, RPRef.concat__rp_helper_79736bdc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.concat RPRef.concat RPRef.concat__rp_helper_79736bdc RPOrig.concat.loop RPRef.concat__rp_helper_79736bdc.loop; rfl))
