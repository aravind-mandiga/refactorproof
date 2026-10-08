-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LinearSearch3_precond (a : Array Int) (P : Int -> Bool) : Prop :=
  -- !benchmark @start precond
  ∃ i, i < a.size ∧ P (a[i]!)
  -- !benchmark @end precond



namespace RPOrig

def LinearSearch3 (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if P (a[n]!) then n else loop (n + 1)
    else
      0
  loop 0
end RPOrig

namespace RPRef
private def LinearSearch3__rp_helper_7883d640 (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if P (a[n]!) then n else loop (n + 1)
    else
      0
  loop 0

def LinearSearch3 (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) : Nat :=
  LinearSearch3__rp_helper_7883d640 a P h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    RPOrig.LinearSearch3 a P h_precond = RPRef.LinearSearch3 a P h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    RPOrig.LinearSearch3 a P h_precond = RPRef.LinearSearch3 a P h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    RPOrig.LinearSearch3 a P h_precond = RPRef.LinearSearch3 a P h_precond := by
  delta RPOrig.LinearSearch3 RPRef.LinearSearch3 RPRef.LinearSearch3__rp_helper_7883d640 RPOrig.LinearSearch3.loop RPRef.LinearSearch3__rp_helper_7883d640.loop
  rfl

theorem rp_equiv_simp_only (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    RPOrig.LinearSearch3 a P h_precond = RPRef.LinearSearch3 a P h_precond := by
  (simp only [RPOrig.LinearSearch3, RPRef.LinearSearch3, RPRef.LinearSearch3__rp_helper_7883d640]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch3 RPRef.LinearSearch3 RPRef.LinearSearch3__rp_helper_7883d640 RPOrig.LinearSearch3.loop RPRef.LinearSearch3__rp_helper_7883d640.loop; rfl))

theorem rp_equiv_simp (a : Array Int) (P : Int -> Bool) (h_precond : LinearSearch3_precond (a) (P)) :
    RPOrig.LinearSearch3 a P h_precond = RPRef.LinearSearch3 a P h_precond := by
  (simp [RPOrig.LinearSearch3, RPRef.LinearSearch3, RPRef.LinearSearch3__rp_helper_7883d640]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch3 RPRef.LinearSearch3 RPRef.LinearSearch3__rp_helper_7883d640 RPOrig.LinearSearch3.loop RPRef.LinearSearch3__rp_helper_7883d640.loop; rfl))
