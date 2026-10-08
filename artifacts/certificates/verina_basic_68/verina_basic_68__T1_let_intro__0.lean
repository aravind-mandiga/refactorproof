-- !benchmark @start import type=solution
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if n < a.size then
      if a[n]! = e then n
      else loop (n + 1)
    else n
  loop 0
end RPOrig

namespace RPRef

def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  let __rp_tmp_dfe96427 : Nat :=
    let rec loop (n : Nat) : Nat :=
      if n < a.size then
        if a[n]! = e then n
        else loop (n + 1)
      else n
    loop 0
  __rp_tmp_dfe96427
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := by
  delta RPOrig.LinearSearch RPRef.LinearSearch RPOrig.LinearSearch.loop RPRef.LinearSearch.loop
  rfl

theorem rp_equiv_simp_only (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := by
  (simp only [RPOrig.LinearSearch, RPRef.LinearSearch]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch RPRef.LinearSearch RPOrig.LinearSearch.loop RPRef.LinearSearch.loop; rfl))

theorem rp_equiv_simp (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := by
  (simp [RPOrig.LinearSearch, RPRef.LinearSearch]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch RPRef.LinearSearch RPOrig.LinearSearch.loop RPRef.LinearSearch.loop; rfl))
