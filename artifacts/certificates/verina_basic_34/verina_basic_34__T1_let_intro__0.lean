-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isEven (n : Int) : Bool :=
  n % 2 = 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findEvenNumbers_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def findEvenNumbers (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) : Array Int :=
  arr.foldl (fun acc x => if isEven x then acc.push x else acc) #[]
end RPOrig

namespace RPRef

def findEvenNumbers (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) : Array Int :=
  let __rp_tmp_fce715a2 : Array Int :=
    arr.foldl (fun acc x => if isEven x then acc.push x else acc) #[]
  __rp_tmp_fce715a2
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) :
    RPOrig.findEvenNumbers arr h_precond = RPRef.findEvenNumbers arr h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) :
    RPOrig.findEvenNumbers arr h_precond = RPRef.findEvenNumbers arr h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) :
    RPOrig.findEvenNumbers arr h_precond = RPRef.findEvenNumbers arr h_precond := by
  delta RPOrig.findEvenNumbers RPRef.findEvenNumbers
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) :
    RPOrig.findEvenNumbers arr h_precond = RPRef.findEvenNumbers arr h_precond := by
  (simp only [RPOrig.findEvenNumbers, RPRef.findEvenNumbers]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findEvenNumbers RPRef.findEvenNumbers; rfl))

theorem rp_equiv_simp (arr : Array Int) (h_precond : findEvenNumbers_precond (arr)) :
    RPOrig.findEvenNumbers arr h_precond = RPRef.findEvenNumbers arr h_precond := by
  (simp [RPOrig.findEvenNumbers, RPRef.findEvenNumbers]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findEvenNumbers RPRef.findEvenNumbers; rfl))
