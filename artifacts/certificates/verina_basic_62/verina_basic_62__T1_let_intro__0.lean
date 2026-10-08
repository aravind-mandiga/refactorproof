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

def Find (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) : Int :=
  let __rp_tmp_16fbb912 : Int :=
    let rec search (index : Nat) : Int :=
      if index < a.size then
        if a[index]! = key then Int.ofNat index
        else search (index + 1)
      else -1
    search 0
  __rp_tmp_16fbb912
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := by
  delta RPOrig.Find RPRef.Find RPOrig.Find.search RPRef.Find.search
  rfl

theorem rp_equiv_simp_only (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := by
  (simp only [RPOrig.Find, RPRef.Find]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Find RPRef.Find RPOrig.Find.search RPRef.Find.search; rfl))

theorem rp_equiv_simp (a : Array Int) (key : Int) (h_precond : Find_precond (a) (key)) :
    RPOrig.Find a key h_precond = RPRef.Find a key h_precond := by
  (simp [RPOrig.Find, RPRef.Find]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.Find RPRef.Find RPOrig.Find.search RPRef.Find.search; rfl))
