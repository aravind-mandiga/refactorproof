-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def modify_array_element_precond (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) : Prop :=
  -- !benchmark @start precond
  index1 < arr.size ∧
  index2 < (arr[index1]!).size
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def updateInner (a : Array Nat) (idx val : Nat) : Array Nat :=
  a.set! idx val

namespace RPOrig

def modify_array_element (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) : Array (Array Nat) :=
  let inner := arr[index1]!
  let inner' := updateInner inner index2 val
  arr.set! index1 inner'
end RPOrig

namespace RPRef

private def modify_array_element__rp_helper_e82921e6 (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) : Array (Array Nat) :=
  let inner := arr[index1]!
  let inner' := updateInner inner index2 val
  arr.set! index1 inner'

def modify_array_element (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) : Array (Array Nat) :=
  modify_array_element__rp_helper_e82921e6 arr index1 index2 val h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) :
    RPOrig.modify_array_element arr index1 index2 val h_precond = RPRef.modify_array_element arr index1 index2 val h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) :
    RPOrig.modify_array_element arr index1 index2 val h_precond = RPRef.modify_array_element arr index1 index2 val h_precond := rfl

theorem rp_equiv_delta_rfl (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) :
    RPOrig.modify_array_element arr index1 index2 val h_precond = RPRef.modify_array_element arr index1 index2 val h_precond := by
  delta RPOrig.modify_array_element RPRef.modify_array_element RPRef.modify_array_element__rp_helper_e82921e6
  rfl

theorem rp_equiv_simp_only (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) :
    RPOrig.modify_array_element arr index1 index2 val h_precond = RPRef.modify_array_element arr index1 index2 val h_precond := by
  (simp only [RPOrig.modify_array_element, RPRef.modify_array_element, RPRef.modify_array_element__rp_helper_e82921e6]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.modify_array_element RPRef.modify_array_element RPRef.modify_array_element__rp_helper_e82921e6; rfl))

theorem rp_equiv_simp (arr : Array (Array Nat)) (index1 : Nat) (index2 : Nat) (val : Nat) (h_precond : modify_array_element_precond (arr) (index1) (index2) (val)) :
    RPOrig.modify_array_element arr index1 index2 val h_precond = RPRef.modify_array_element arr index1 index2 val h_precond := by
  (simp [RPOrig.modify_array_element, RPRef.modify_array_element, RPRef.modify_array_element__rp_helper_e82921e6]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.modify_array_element RPRef.modify_array_element RPRef.modify_array_element__rp_helper_e82921e6; rfl))
