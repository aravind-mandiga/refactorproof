-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux
@[reducible, simp]
def get2d (a : Array (Array Int)) (i j : Int) : Int :=
  (a[Int.toNat i]!)[Int.toNat j]!
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux
-- !benchmark @end precond_aux

@[reducible, simp]
def SlopeSearch_precond (a : Array (Array Int)) (key : Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0 ∧
  (a[0]!).size > 0 ∧  -- non-empty inner arrays
  List.Pairwise (·.size = ·.size) a.toList ∧
  a.all (fun x => List.Pairwise (· ≤ ·) x.toList) ∧
  (List.range (a[0]!.size)).all (fun i =>
    List.Pairwise (· ≤ ·) (a.map (fun x => x[i]!)).toList
  )
  -- !benchmark @end precond



namespace RPOrig

def SlopeSearch (a : Array (Array Int)) (key : Int) (h_precond : SlopeSearch_precond (a) (key)) : (Int × Int) :=
  let rows := a.size
  let cols := if rows > 0 then (a[0]!).size else 0

  let rec aux (m n : Int) (fuel : Nat) : (Int × Int) :=
    if fuel = 0 then (-1, -1)
    else if m ≥ Int.ofNat rows || n < 0 then (-1, -1)
    else if get2d a m n = key then (m, n)
    else if get2d a m n < key then
      aux (m + 1) n (fuel - 1)
    else
      aux m (n - 1) (fuel - 1)

  aux 0 (Int.ofNat (cols - 1)) (rows + cols)
end RPOrig

namespace RPRef

def SlopeSearch (a : Array (Array Int)) (key : Int) (h_precond : SlopeSearch_precond (a) (key)) : (Int × Int) :=
  let rows := a.size
  let cols := if rows > 0 then (a[0]!).size else 0

  let rec aux (m n : Int) (fuel : Nat) : (Int × Int) :=
    if fuel = 0 then (-1, -1)
    else if m ≥ Int.ofNat rows || n < 0 then (-1, -1)
    else if get2d a m n = key then (m, n)
    else if get2d a m n < key then
      aux (1 + m) n (fuel - 1)
    else
      aux m (n - 1) (fuel - 1)

  aux 0 (Int.ofNat (cols - 1)) (rows + cols)
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (a : Array (Array Int)) (key : Int) (h_precond : SlopeSearch_precond (a) (key)) :
    RPOrig.SlopeSearch a key h_precond = RPRef.SlopeSearch a key h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (a : Array (Array Int)) (key : Int) (h_precond : SlopeSearch_precond (a) (key)) :
    RPOrig.SlopeSearch a key h_precond = RPRef.SlopeSearch a key h_precond := rfl

theorem rp_equiv_delta_rfl (a : Array (Array Int)) (key : Int) (h_precond : SlopeSearch_precond (a) (key)) :
    RPOrig.SlopeSearch a key h_precond = RPRef.SlopeSearch a key h_precond := by
  delta RPOrig.SlopeSearch RPRef.SlopeSearch RPOrig.SlopeSearch.aux RPRef.SlopeSearch.aux
  rfl

theorem rp_equiv_simp_only (a : Array (Array Int)) (key : Int) (h_precond : SlopeSearch_precond (a) (key)) :
    RPOrig.SlopeSearch a key h_precond = RPRef.SlopeSearch a key h_precond := by
  first
    | (simp only [RPOrig.SlopeSearch, RPRef.SlopeSearch, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SlopeSearch RPRef.SlopeSearch RPOrig.SlopeSearch.aux RPRef.SlopeSearch.aux; rfl))
    | (simp only [RPOrig.SlopeSearch, RPRef.SlopeSearch, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SlopeSearch RPRef.SlopeSearch RPOrig.SlopeSearch.aux RPRef.SlopeSearch.aux; rfl))
    | (simp only [RPOrig.SlopeSearch, RPRef.SlopeSearch, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SlopeSearch RPRef.SlopeSearch RPOrig.SlopeSearch.aux RPRef.SlopeSearch.aux; rfl))
    | (simp only [RPOrig.SlopeSearch, RPRef.SlopeSearch]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SlopeSearch RPRef.SlopeSearch RPOrig.SlopeSearch.aux RPRef.SlopeSearch.aux; rfl))

theorem rp_equiv_simp (a : Array (Array Int)) (key : Int) (h_precond : SlopeSearch_precond (a) (key)) :
    RPOrig.SlopeSearch a key h_precond = RPRef.SlopeSearch a key h_precond := by
  first
    | (simp [RPOrig.SlopeSearch, RPRef.SlopeSearch, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SlopeSearch RPRef.SlopeSearch RPOrig.SlopeSearch.aux RPRef.SlopeSearch.aux; rfl))
    | (simp [RPOrig.SlopeSearch, RPRef.SlopeSearch, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc, Bool.or_comm, Bool.or_left_comm, Bool.or_assoc, and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SlopeSearch RPRef.SlopeSearch RPOrig.SlopeSearch.aux RPRef.SlopeSearch.aux; rfl))
    | (simp [RPOrig.SlopeSearch, RPRef.SlopeSearch, Nat.add_comm, Int.add_comm, Nat.mul_comm, Int.mul_comm, Bool.and_comm, Bool.or_comm, and_comm, or_comm]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SlopeSearch RPRef.SlopeSearch RPOrig.SlopeSearch.aux RPRef.SlopeSearch.aux; rfl))
    | (simp [RPOrig.SlopeSearch, RPRef.SlopeSearch]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SlopeSearch RPRef.SlopeSearch RPOrig.SlopeSearch.aux RPRef.SlopeSearch.aux; rfl))

theorem rp_equiv_ac_rfl (a : Array (Array Int)) (key : Int) (h_precond : SlopeSearch_precond (a) (key)) :
    RPOrig.SlopeSearch a key h_precond = RPRef.SlopeSearch a key h_precond := by
  (try simp only [RPOrig.SlopeSearch, RPRef.SlopeSearch]) <;> (try ac_nf) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.SlopeSearch RPRef.SlopeSearch RPOrig.SlopeSearch.aux RPRef.SlopeSearch.aux; rfl))
