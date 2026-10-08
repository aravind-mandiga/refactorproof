-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def LinearSearch_precond (a : Array Int) (e : Int) : Prop :=
  -- !benchmark @start precond
  ∃ i, i < a.size ∧ a[i]! = e
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def linearSearchAux (a : Array Int) (e : Int) (n : Nat) : Nat :=
  if n < a.size then
    if a[n]! = e then n else linearSearchAux a e (n + 1)
  else
    0

namespace RPOrig

def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  linearSearchAux a e 0
end RPOrig

namespace RPRef

def LinearSearch (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) : Nat :=
  let __rp_tmp_f7ec7460 : Nat :=
    linearSearchAux a e 0
  __rp_tmp_f7ec7460
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := by
  delta RPOrig.LinearSearch RPRef.LinearSearch
  rfl

theorem rp_equiv_simp_only (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := by
  (simp only [RPOrig.LinearSearch, RPRef.LinearSearch]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch RPRef.LinearSearch; rfl))

theorem rp_equiv_simp (a : Array Int) (e : Int) (h_precond : LinearSearch_precond (a) (e)) :
    RPOrig.LinearSearch a e h_precond = RPRef.LinearSearch a e h_precond := by
  (simp [RPOrig.LinearSearch, RPRef.LinearSearch]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.LinearSearch RPRef.LinearSearch; rfl))
