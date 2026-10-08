-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def hasChordIntersection_precond (N : Nat) (chords : List (List Nat)) : Prop :=
  -- !benchmark @start precond
  N ≥ 2 ∧
  chords.length = N ∧
  chords.all (fun chord => chord.length = 2 ∧ chord[0]! ≥ 1 ∧ chord[0]! ≤ 2 * N ∧ chord[1]! ≥ 1 ∧ chord[1]! ≤ 2 * N) ∧
  List.Nodup (chords.flatMap id)
  -- !benchmark @end precond



namespace RPOrig

def hasChordIntersection (N : Nat) (chords : List (List Nat)) (h_precond : hasChordIntersection_precond (N) (chords)) : Bool :=
  let sortedChords := chords.map (fun chord =>
    let a := chord[0]!
    let b := chord[1]!
    if a > b then [b, a] else [a, b]
  )

  let rec checkIntersection (stack : List (List Nat)) (remaining : List (List Nat)) : Bool :=
    match remaining with
    | [] => false
    | chord :: rest =>
      let a := chord[0]!
      let b := chord[1]!
      let newStack := stack.dropWhile (fun c => (c)[1]! < a)
      match newStack with
      | [] => checkIntersection (chord :: newStack) rest
      | top :: _ =>
        if top[1]! > a && top[1]! < b then
          true
        else
          checkIntersection (chord :: newStack) rest

  let rec insert (x : List Nat) (xs : List (List Nat)) : List (List Nat) :=
    match xs with
    | [] => [x]
    | y :: ys => if x[0]! < y[0]! then x :: xs else y :: insert x ys

  let rec sort (xs : List (List Nat)) : List (List Nat) :=
    match xs with
    | [] => []
    | x :: xs => insert x (sort xs)

  let sortedChords := sort sortedChords
  checkIntersection [] sortedChords
end RPOrig

namespace RPRef

def hasChordIntersection (N : Nat) (chords : List (List Nat)) (h_precond : hasChordIntersection_precond (N) (chords)) : Bool :=
  let __rp_tmp_d2a5e62f : Bool :=
    let sortedChords := chords.map (fun chord =>
      let a := chord[0]!
      let b := chord[1]!
      if a > b then [b, a] else [a, b]
    )

    let rec checkIntersection (stack : List (List Nat)) (remaining : List (List Nat)) : Bool :=
      match remaining with
      | [] => false
      | chord :: rest =>
        let a := chord[0]!
        let b := chord[1]!
        let newStack := stack.dropWhile (fun c => (c)[1]! < a)
        match newStack with
        | [] => checkIntersection (chord :: newStack) rest
        | top :: _ =>
          if top[1]! > a && top[1]! < b then
            true
          else
            checkIntersection (chord :: newStack) rest

    let rec insert (x : List Nat) (xs : List (List Nat)) : List (List Nat) :=
      match xs with
      | [] => [x]
      | y :: ys => if x[0]! < y[0]! then x :: xs else y :: insert x ys

    let rec sort (xs : List (List Nat)) : List (List Nat) :=
      match xs with
      | [] => []
      | x :: xs => insert x (sort xs)

    let sortedChords := sort sortedChords
    checkIntersection [] sortedChords
  __rp_tmp_d2a5e62f
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (N : Nat) (chords : List (List Nat)) (h_precond : hasChordIntersection_precond (N) (chords)) :
    RPOrig.hasChordIntersection N chords h_precond = RPRef.hasChordIntersection N chords h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (N : Nat) (chords : List (List Nat)) (h_precond : hasChordIntersection_precond (N) (chords)) :
    RPOrig.hasChordIntersection N chords h_precond = RPRef.hasChordIntersection N chords h_precond := rfl

theorem rp_equiv_delta_rfl (N : Nat) (chords : List (List Nat)) (h_precond : hasChordIntersection_precond (N) (chords)) :
    RPOrig.hasChordIntersection N chords h_precond = RPRef.hasChordIntersection N chords h_precond := by
  delta RPOrig.hasChordIntersection RPRef.hasChordIntersection RPOrig.hasChordIntersection.checkIntersection RPOrig.hasChordIntersection.insert RPOrig.hasChordIntersection.sort RPRef.hasChordIntersection.checkIntersection RPRef.hasChordIntersection.insert RPRef.hasChordIntersection.sort
  rfl

theorem rp_equiv_simp_only (N : Nat) (chords : List (List Nat)) (h_precond : hasChordIntersection_precond (N) (chords)) :
    RPOrig.hasChordIntersection N chords h_precond = RPRef.hasChordIntersection N chords h_precond := by
  (simp only [RPOrig.hasChordIntersection, RPRef.hasChordIntersection]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasChordIntersection RPRef.hasChordIntersection RPOrig.hasChordIntersection.checkIntersection RPOrig.hasChordIntersection.insert RPOrig.hasChordIntersection.sort RPRef.hasChordIntersection.checkIntersection RPRef.hasChordIntersection.insert RPRef.hasChordIntersection.sort; rfl))

theorem rp_equiv_simp (N : Nat) (chords : List (List Nat)) (h_precond : hasChordIntersection_precond (N) (chords)) :
    RPOrig.hasChordIntersection N chords h_precond = RPRef.hasChordIntersection N chords h_precond := by
  (simp [RPOrig.hasChordIntersection, RPRef.hasChordIntersection]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.hasChordIntersection RPRef.hasChordIntersection RPOrig.hasChordIntersection.checkIntersection RPOrig.hasChordIntersection.insert RPOrig.hasChordIntersection.sort RPRef.hasChordIntersection.checkIntersection RPRef.hasChordIntersection.insert RPRef.hasChordIntersection.sort; rfl))
