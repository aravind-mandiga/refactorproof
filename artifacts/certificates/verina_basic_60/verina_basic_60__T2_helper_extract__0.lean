-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isEven (n : Int) : Bool :=
  n % 2 = 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def FindEvenNumbers_precond (arr : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def FindEvenNumbers (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) : Array Int :=
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < arr.size then
      if isEven (arr.getD i 0) then
        loop (i + 1) (acc.push (arr.getD i 0))
      else
        loop (i + 1) acc
    else
      acc
  loop 0 (Array.mkEmpty 0)
end RPOrig

namespace RPRef
private def FindEvenNumbers__rp_helper_9ca1e9a3 (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) : Array Int :=
  let rec loop (i : Nat) (acc : Array Int) : Array Int :=
    if i < arr.size then
      if isEven (arr.getD i 0) then
        loop (i + 1) (acc.push (arr.getD i 0))
      else
        loop (i + 1) acc
    else
      acc
  loop 0 (Array.mkEmpty 0)

def FindEvenNumbers (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) : Array Int :=
  FindEvenNumbers__rp_helper_9ca1e9a3 arr h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    RPOrig.FindEvenNumbers arr h_precond = RPRef.FindEvenNumbers arr h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    RPOrig.FindEvenNumbers arr h_precond = RPRef.FindEvenNumbers arr h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    RPOrig.FindEvenNumbers arr h_precond = RPRef.FindEvenNumbers arr h_precond := by
  delta RPOrig.FindEvenNumbers RPRef.FindEvenNumbers RPRef.FindEvenNumbers__rp_helper_9ca1e9a3 RPOrig.FindEvenNumbers.loop RPRef.FindEvenNumbers__rp_helper_9ca1e9a3.loop
  rfl

theorem rp_equiv_simp_only (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    RPOrig.FindEvenNumbers arr h_precond = RPRef.FindEvenNumbers arr h_precond := by
  (simp only [RPOrig.FindEvenNumbers, RPRef.FindEvenNumbers, RPRef.FindEvenNumbers__rp_helper_9ca1e9a3]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.FindEvenNumbers RPRef.FindEvenNumbers RPRef.FindEvenNumbers__rp_helper_9ca1e9a3 RPOrig.FindEvenNumbers.loop RPRef.FindEvenNumbers__rp_helper_9ca1e9a3.loop; rfl))

theorem rp_equiv_simp (arr : Array Int) (h_precond : FindEvenNumbers_precond (arr)) :
    RPOrig.FindEvenNumbers arr h_precond = RPRef.FindEvenNumbers arr h_precond := by
  (simp [RPOrig.FindEvenNumbers, RPRef.FindEvenNumbers, RPRef.FindEvenNumbers__rp_helper_9ca1e9a3]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.FindEvenNumbers RPRef.FindEvenNumbers RPRef.FindEvenNumbers__rp_helper_9ca1e9a3 RPOrig.FindEvenNumbers.loop RPRef.FindEvenNumbers__rp_helper_9ca1e9a3.loop; rfl))
