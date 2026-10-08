-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def BubbleSort_precond (a : Array Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def swap (a : Array Int) (i j : Nat) : Array Int :=
  let temp := a[i]!
  let a₁ := a.set! i (a[j]!)
  a₁.set! j temp

def bubbleInner (j i : Nat) (a : Array Int) : Array Int :=
  if j < i then
    let a' := if a[j]! > a[j+1]! then swap a j (j+1) else a
    bubbleInner (j+1) i a'
  else
    a

def bubbleOuter (i : Nat) (a : Array Int) : Array Int :=
  if i > 0 then
    let a' := bubbleInner 0 i a
    bubbleOuter (i - 1) a'
  else
    a

namespace RPOrig

def BubbleSort (a : Array Int) (h_precond : BubbleSort_precond (a)) : Array Int :=
  if a.size = 0 then a else bubbleOuter (a.size - 1) a
end RPOrig

namespace RPRef

def BubbleSort (a : Array Int) (h_precond : BubbleSort_precond (a)) : Array Int :=
  let __rp_tmp_b012b47d : Array Int :=
    if a.size = 0 then a else bubbleOuter (a.size - 1) a
  __rp_tmp_b012b47d
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array Int) (h_precond : BubbleSort_precond (a)) :
    RPOrig.BubbleSort a h_precond = RPRef.BubbleSort a h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array Int) (h_precond : BubbleSort_precond (a)) :
    RPOrig.BubbleSort a h_precond = RPRef.BubbleSort a h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array Int) (h_precond : BubbleSort_precond (a)) :
    RPOrig.BubbleSort a h_precond = RPRef.BubbleSort a h_precond := by
  delta RPOrig.BubbleSort RPRef.BubbleSort
  rfl

theorem rp_equiv_simp_only (a : Array Int) (h_precond : BubbleSort_precond (a)) :
    RPOrig.BubbleSort a h_precond = RPRef.BubbleSort a h_precond := by
  (simp only [RPOrig.BubbleSort, RPRef.BubbleSort]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.BubbleSort RPRef.BubbleSort; rfl))

theorem rp_equiv_simp (a : Array Int) (h_precond : BubbleSort_precond (a)) :
    RPOrig.BubbleSort a h_precond = RPRef.BubbleSort a h_precond := by
  (simp [RPOrig.BubbleSort, RPRef.BubbleSort]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.BubbleSort RPRef.BubbleSort; rfl))
