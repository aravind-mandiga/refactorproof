-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def nthUglyNumber_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  n > 0
  -- !benchmark @end precond



-- shared (unchanged) implementation helpers
def nextUgly (seq : List Nat) (c2 c3 c5 : Nat) : (Nat × Nat × Nat × Nat) :=
  let i2 := seq[c2]! * 2
  let i3 := seq[c3]! * 3
  let i5 := seq[c5]! * 5
  let next := min i2 (min i3 i5)
  let c2' := if next = i2 then c2 + 1 else c2
  let c3' := if next = i3 then c3 + 1 else c3
  let c5' := if next = i5 then c5 + 1 else c5
  (next, c2', c3', c5')


namespace RPOrig

def nthUglyNumber (n : Nat) (h_precond : nthUglyNumber_precond (n)) : Nat :=
  let rec loop (i : Nat) (seq : List Nat) (c2 c3 c5 : Nat) : List Nat :=
    match i with
    | 0 => seq
    | Nat.succ i' =>
      let (next, c2', c3', c5') := nextUgly seq c2 c3 c5
      loop i' (seq ++ [next]) c2' c3' c5'
  (loop (n - 1) [1] 0 0 0)[(n - 1)]!
end RPOrig

namespace RPRef

def nthUglyNumber (n : Nat) (h_precond : nthUglyNumber_precond (n)) : Nat :=
  let __rp_tmp_7efe92ed : Nat :=
    let rec loop (i : Nat) (seq : List Nat) (c2 c3 c5 : Nat) : List Nat :=
      match i with
      | 0 => seq
      | Nat.succ i' =>
        let (next, c2', c3', c5') := nextUgly seq c2 c3 c5
        loop i' (seq ++ [next]) c2' c3' c5'
    (loop (n - 1) [1] 0 0 0)[(n - 1)]!
  __rp_tmp_7efe92ed
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (n : Nat) (h_precond : nthUglyNumber_precond (n)) :
    RPOrig.nthUglyNumber n h_precond = RPRef.nthUglyNumber n h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (n : Nat) (h_precond : nthUglyNumber_precond (n)) :
    RPOrig.nthUglyNumber n h_precond = RPRef.nthUglyNumber n h_precond := rfl

theorem rp_equiv_delta_rfl (n : Nat) (h_precond : nthUglyNumber_precond (n)) :
    RPOrig.nthUglyNumber n h_precond = RPRef.nthUglyNumber n h_precond := by
  delta RPOrig.nthUglyNumber RPRef.nthUglyNumber RPOrig.nthUglyNumber.loop RPRef.nthUglyNumber.loop
  rfl

theorem rp_equiv_simp_only (n : Nat) (h_precond : nthUglyNumber_precond (n)) :
    RPOrig.nthUglyNumber n h_precond = RPRef.nthUglyNumber n h_precond := by
  (simp only [RPOrig.nthUglyNumber, RPRef.nthUglyNumber]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.nthUglyNumber RPRef.nthUglyNumber RPOrig.nthUglyNumber.loop RPRef.nthUglyNumber.loop; rfl))

theorem rp_equiv_simp (n : Nat) (h_precond : nthUglyNumber_precond (n)) :
    RPOrig.nthUglyNumber n h_precond = RPRef.nthUglyNumber n h_precond := by
  (simp [RPOrig.nthUglyNumber, RPRef.nthUglyNumber]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.nthUglyNumber RPRef.nthUglyNumber RPOrig.nthUglyNumber.loop RPRef.nthUglyNumber.loop; rfl))
