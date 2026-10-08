-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Compare_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



namespace RPOrig

def Compare (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  if a = b then true else false
end RPOrig

namespace RPRef
private def Compare__rp_branch_e4570326 (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  false

def Compare (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  if a = b then true else
    Compare__rp_branch_e4570326 a b h_precond
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) :
    RPOrig.Compare a b h_precond = RPRef.Compare a b h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) :
    RPOrig.Compare a b h_precond = RPRef.Compare a b h_precond := rfl

theorem rp_equiv_delta_rfl (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) :
    RPOrig.Compare a b h_precond = RPRef.Compare a b h_precond := by
  first
    | (delta RPOrig.Compare RPRef.Compare RPRef.Compare__rp_branch_e4570326; rfl)
    | (delta RPOrig.Compare RPRef.Compare RPRef.Compare__rp_branch_e4570326 RPOrig.Compare._unary; rfl)
    | (set_option smartUnfolding false in rfl)

theorem rp_equiv_simp_only (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) :
    RPOrig.Compare a b h_precond = RPRef.Compare a b h_precond := by
  (simp only [RPOrig.Compare, RPRef.Compare, RPRef.Compare__rp_branch_e4570326]) <;> (first | rfl | (delta RPOrig.Compare RPRef.Compare RPRef.Compare__rp_branch_e4570326; rfl) | (delta RPOrig.Compare RPRef.Compare RPRef.Compare__rp_branch_e4570326 RPOrig.Compare._unary; rfl) | (set_option smartUnfolding false in rfl))

theorem rp_equiv_simp (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) :
    RPOrig.Compare a b h_precond = RPRef.Compare a b h_precond := by
  (simp [RPOrig.Compare, RPRef.Compare, RPRef.Compare__rp_branch_e4570326]) <;> (first | rfl | (delta RPOrig.Compare RPRef.Compare RPRef.Compare__rp_branch_e4570326; rfl) | (delta RPOrig.Compare RPRef.Compare RPRef.Compare__rp_branch_e4570326 RPOrig.Compare._unary; rfl) | (set_option smartUnfolding false in rfl))
