-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
def isOdd (x : Int) : Bool :=
  x % 2 ≠ 0
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def findFirstOdd_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond



namespace RPOrig

def findFirstOdd (a : Array Int) (h_precond : findFirstOdd_precond (a)) : Option Nat :=
  -- Creates list of (index, value) pairs
  let indexed := a.toList.zipIdx

  -- Find the first pair where the value is odd
  let found := List.find? (fun (x, _) => isOdd x) indexed

  -- Extract the index from the found pair (if any)
  Option.map (fun (_, i) => i) found
end RPOrig

namespace RPRef
private def findFirstOdd__rp_helper_ae0c5502 (a : Array Int) (h_precond : findFirstOdd_precond (a)) : Option Nat :=
  -- Creates list of (index, value) pairs
  let indexed := a.toList.zipIdx

  -- Find the first pair where the value is odd
  let found := List.find? (fun (x, _) => isOdd x) indexed

  -- Extract the index from the found pair (if any)
  Option.map (fun (_, i) => i) found

def findFirstOdd (a : Array Int) (h_precond : findFirstOdd_precond (a)) : Option Nat :=
  findFirstOdd__rp_helper_ae0c5502 a h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : findFirstOdd_precond (a)) :
    RPOrig.findFirstOdd a h_precond = RPRef.findFirstOdd a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : findFirstOdd_precond (a)) :
    RPOrig.findFirstOdd a h_precond = RPRef.findFirstOdd a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : findFirstOdd_precond (a)) :
    RPOrig.findFirstOdd a h_precond = RPRef.findFirstOdd a h_precond := by
  delta RPOrig.findFirstOdd RPRef.findFirstOdd RPRef.findFirstOdd__rp_helper_ae0c5502
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : findFirstOdd_precond (a)) :
    RPOrig.findFirstOdd a h_precond = RPRef.findFirstOdd a h_precond := by
  (simp only [RPOrig.findFirstOdd, RPRef.findFirstOdd, RPRef.findFirstOdd__rp_helper_ae0c5502]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstOdd RPRef.findFirstOdd RPRef.findFirstOdd__rp_helper_ae0c5502; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : findFirstOdd_precond (a)) :
    RPOrig.findFirstOdd a h_precond = RPRef.findFirstOdd a h_precond := by
  (simp [RPOrig.findFirstOdd, RPRef.findFirstOdd, RPRef.findFirstOdd__rp_helper_ae0c5502]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.findFirstOdd RPRef.findFirstOdd RPRef.findFirstOdd__rp_helper_ae0c5502; rfl))
