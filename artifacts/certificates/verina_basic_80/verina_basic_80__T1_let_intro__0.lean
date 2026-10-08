-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def only_once_precond (a : Array Int) (key : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def only_once_loop {T : Type} [DecidableEq T] (a : Array T) (key : T) (i keyCount : Nat) : Bool :=
  if i < a.size then
    match a[i]? with
    | some val =>
        let newCount := if val = key then keyCount + 1 else keyCount
        only_once_loop a key (i + 1) newCount
    | none => keyCount == 1
  else
    keyCount == 1

namespace RPOrig

def only_once (a : Array Int) (key : Int) (h_precond : only_once_precond (a) (key)) : Bool :=
  only_once_loop a key 0 0
end RPOrig

namespace RPRef

def only_once (a : Array Int) (key : Int) (h_precond : only_once_precond (a) (key)) : Bool :=
  let __rp_tmp_8b0e79bf : Bool :=
    only_once_loop a key 0 0
  __rp_tmp_8b0e79bf
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (key : Int) (h_precond : only_once_precond (a) (key)) :
    RPOrig.only_once a key h_precond = RPRef.only_once a key h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (key : Int) (h_precond : only_once_precond (a) (key)) :
    RPOrig.only_once a key h_precond = RPRef.only_once a key h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (key : Int) (h_precond : only_once_precond (a) (key)) :
    RPOrig.only_once a key h_precond = RPRef.only_once a key h_precond := by
  delta RPOrig.only_once RPRef.only_once
  rfl

theorem rp_equiv_simp_only (a : Array Int) (key : Int) (h_precond : only_once_precond (a) (key)) :
    RPOrig.only_once a key h_precond = RPRef.only_once a key h_precond := by
  (simp only [RPOrig.only_once, RPRef.only_once]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.only_once RPRef.only_once; rfl))

theorem rp_equiv_simp (a : Array Int) (key : Int) (h_precond : only_once_precond (a) (key)) :
    RPOrig.only_once a key h_precond = RPRef.only_once a key h_precond := by
  (simp [RPOrig.only_once, RPRef.only_once]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.only_once RPRef.only_once; rfl))
