-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def topKFrequent_precond (nums : List Int) (k : Nat) : Prop :=
  -- !benchmark @start precond
  k ≤ nums.eraseDups.length
  -- !benchmark @end precond



namespace RPOrig

def topKFrequent (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond (nums) (k)) : List Int :=
  -- Build frequency list maintaining first occurrence order (deterministic)
  let freqList : List (Int × Nat) :=
    nums.foldl (init := []) fun acc n =>
      match acc.find? (fun (key, _) => key == n) with
      | some _ => acc.map (fun (key, cnt) => if key == n then (key, cnt + 1) else (key, cnt))
      | none => acc ++ [(n, 1)]
  -- Sort by frequency (descending), stable sort preserves first-occurrence order for ties
  let sorted := freqList.foldl
    (fun acc pair =>
      let (x, cx) := pair
      let rec insertSorted (xs : List (Int × Nat)) : List (Int × Nat) :=
        match xs with
        | [] => [pair]
        | (y, cy) :: ys =>
          if cx > cy then
            pair :: (y, cy) :: ys
          else
            (y, cy) :: insertSorted ys
      insertSorted acc
    ) []

  sorted.take k |>.map (fun (n, _) => n)
end RPOrig

namespace RPRef

def topKFrequent (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond (nums) (k)) : List Int :=
  -- Build frequency list maintaining first occurrence order (deterministic)
  let freqList : List (Int × Nat) :=
    nums.foldl (init := []) fun acc n =>
      match acc.find? (fun (key, _) => key == n) with
      | some _ => acc.map (fun (key, cnt) => if key == n then (key, 1 + cnt) else (key, cnt))
      | none => acc ++ [(n, 1)]
  -- Sort by frequency (descending), stable sort preserves first-occurrence order for ties
  let sorted := freqList.foldl
    (fun acc pair =>
      let (x, cx) := pair
      let rec insertSorted (xs : List (Int × Nat)) : List (Int × Nat) :=
        match xs with
        | [] => [pair]
        | (y, cy) :: ys =>
          if cx > cy then
            pair :: (y, cy) :: ys
          else
            (y, cy) :: insertSorted ys
      insertSorted acc
    ) []

  sorted.take k |>.map (fun (n, _) => n)
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond (nums) (k)) :
    RPOrig.topKFrequent nums k h_precond = RPRef.topKFrequent nums k h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond (nums) (k)) :
    RPOrig.topKFrequent nums k h_precond = RPRef.topKFrequent nums k h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond (nums) (k)) :
    RPOrig.topKFrequent nums k h_precond = RPRef.topKFrequent nums k h_precond := by
  delta RPOrig.topKFrequent RPRef.topKFrequent RPOrig.topKFrequent.insertSorted RPRef.topKFrequent.insertSorted
  rfl

theorem rp_equiv_simp_only (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond (nums) (k)) :
    RPOrig.topKFrequent nums k h_precond = RPRef.topKFrequent nums k h_precond := by
  first
    | (simp only [RPOrig.topKFrequent, RPRef.topKFrequent, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.topKFrequent RPRef.topKFrequent RPOrig.topKFrequent.insertSorted RPRef.topKFrequent.insertSorted; rfl))
    | (simp only [RPOrig.topKFrequent, RPRef.topKFrequent, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.topKFrequent RPRef.topKFrequent RPOrig.topKFrequent.insertSorted RPRef.topKFrequent.insertSorted; rfl))
    | (simp only [RPOrig.topKFrequent, RPRef.topKFrequent, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.topKFrequent RPRef.topKFrequent RPOrig.topKFrequent.insertSorted RPRef.topKFrequent.insertSorted; rfl))
    | (simp only [RPOrig.topKFrequent, RPRef.topKFrequent]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.topKFrequent RPRef.topKFrequent RPOrig.topKFrequent.insertSorted RPRef.topKFrequent.insertSorted; rfl))

theorem rp_equiv_simp (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond (nums) (k)) :
    RPOrig.topKFrequent nums k h_precond = RPRef.topKFrequent nums k h_precond := by
  first
    | (simp [RPOrig.topKFrequent, RPRef.topKFrequent, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.topKFrequent RPRef.topKFrequent RPOrig.topKFrequent.insertSorted RPRef.topKFrequent.insertSorted; rfl))
    | (simp [RPOrig.topKFrequent, RPRef.topKFrequent, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.topKFrequent RPRef.topKFrequent RPOrig.topKFrequent.insertSorted RPRef.topKFrequent.insertSorted; rfl))
    | (simp [RPOrig.topKFrequent, RPRef.topKFrequent, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.topKFrequent RPRef.topKFrequent RPOrig.topKFrequent.insertSorted RPRef.topKFrequent.insertSorted; rfl))
    | (simp [RPOrig.topKFrequent, RPRef.topKFrequent]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.topKFrequent RPRef.topKFrequent RPOrig.topKFrequent.insertSorted RPRef.topKFrequent.insertSorted; rfl))

theorem rp_equiv_ac_rfl (nums : List Int) (k : Nat) (h_precond : topKFrequent_precond (nums) (k)) :
    RPOrig.topKFrequent nums k h_precond = RPRef.topKFrequent nums k h_precond := by
  (try simp only [RPOrig.topKFrequent, RPRef.topKFrequent]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.topKFrequent RPRef.topKFrequent RPOrig.topKFrequent.insertSorted RPRef.topKFrequent.insertSorted; rfl))
