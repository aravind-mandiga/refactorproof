-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def below_zero_precond (operations : List Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def buildS (operations : List Int) : Array Int :=
  let sList := operations.foldl
    (fun (acc : List Int) (op : Int) =>
      let last := acc.getLast? |>.getD 0
      acc.append [last + op])
    [0]
  Array.mk sList

namespace RPOrig

def below_zero (operations : List Int) (h_precond : below_zero_precond (operations)) : (Array Int × Bool) :=
  let s := buildS operations
  let rec check_negative (lst : List Int) : Bool :=
    match lst with
    | []      => false
    | x :: xs => if x < 0 then true else check_negative xs
  let result := check_negative (s.toList)
  (s, result)
end RPOrig

namespace RPRef

def below_zero (operations : List Int) (h_precond : below_zero_precond (operations)) : (Array Int × Bool) :=
  let __rp_tmp_b63aa3e9 : (Array Int × Bool) :=
    let s := buildS operations
    let rec check_negative (lst : List Int) : Bool :=
      match lst with
      | []      => false
      | x :: xs => if x < 0 then true else check_negative xs
    let result := check_negative (s.toList)
    (s, result)
  __rp_tmp_b63aa3e9
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (operations : List Int) (h_precond : below_zero_precond (operations)) :
    RPOrig.below_zero operations h_precond = RPRef.below_zero operations h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (operations : List Int) (h_precond : below_zero_precond (operations)) :
    RPOrig.below_zero operations h_precond = RPRef.below_zero operations h_precond := rfl

theorem rp_equiv_delta_rfl (operations : List Int) (h_precond : below_zero_precond (operations)) :
    RPOrig.below_zero operations h_precond = RPRef.below_zero operations h_precond := by
  delta RPOrig.below_zero RPRef.below_zero RPOrig.below_zero.check_negative RPRef.below_zero.check_negative
  rfl

theorem rp_equiv_simp_only (operations : List Int) (h_precond : below_zero_precond (operations)) :
    RPOrig.below_zero operations h_precond = RPRef.below_zero operations h_precond := by
  (simp only [RPOrig.below_zero, RPRef.below_zero]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.below_zero RPRef.below_zero RPOrig.below_zero.check_negative RPRef.below_zero.check_negative; rfl))

theorem rp_equiv_simp (operations : List Int) (h_precond : below_zero_precond (operations)) :
    RPOrig.below_zero operations h_precond = RPRef.below_zero operations h_precond := by
  (simp [RPOrig.below_zero, RPRef.below_zero]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.below_zero RPRef.below_zero RPOrig.below_zero.check_negative RPRef.below_zero.check_negative; rfl))
