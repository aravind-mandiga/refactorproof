-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Find_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def Find (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) : Int :=
  let rec search (index : Nat) : Int :=
    if index < a.size then
      if a[index]! = key then Int.ofNat index
      else search (index + 1)
    else -1
  search 0
end RPOrig

namespace RPRef
private def Find__rp_helper_5211537f (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) : Int :=
  let rec search (index : Nat) : Int :=
    if index < a.size then
      if a[index]! = key then Int.ofNat index
      else search (index + 1)
    else -1
  search 0

def Find (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) : Int :=
  Find__rp_helper_5211537f a key h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := by
  delta RPOrig.Find RPRef.Find RPRef.Find__rp_helper_5211537f RPOrig.Find.search RPRef.Find__rp_helper_5211537f.search
  rfl

theorem rp_equiv_simp_only (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := by
  (simp only [RPOrig.Find, RPRef.Find, RPRef.Find__rp_helper_5211537f]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Find RPRef.Find RPRef.Find__rp_helper_5211537f RPOrig.Find.search RPRef.Find__rp_helper_5211537f.search; rfl))

theorem rp_equiv_simp (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := by
  (simp [RPOrig.Find, RPRef.Find, RPRef.Find__rp_helper_5211537f]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Find RPRef.Find RPRef.Find__rp_helper_5211537f RPOrig.Find.search RPRef.Find__rp_helper_5211537f.search; rfl))
