-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def minOperations_precond (nums : List Nat) (k : Nat) : Prop :=
  -- !benchmark @start precond
  let target_nums := (List.range k).map (· + 1)
  target_nums.all (fun n => List.elem n nums)
  -- !benchmark @end precond



namespace RPOrig

def minOperations (nums : List Nat) (k : Nat) (h_precond : minOperations_precond (nums) (k)) : Nat :=
  -- edge case k=0, requires 0 operations
  if k == 0 then 0 else
  -- recursive helper function
  let rec loop (remaining : List Nat) (collected : List Nat) (collected_count : Nat) (ops : Nat) : Nat :=
    match remaining with
    | [] => ops -- base case
    | head :: tail =>
      let ops' := ops + 1
      -- check if the element is relevant (1 <= head <= k) and not already collected
      -- use a list `collected` to keep track of unique numbers found so far
      if head > 0 && head <= k && !(List.elem head collected) then
          let collected' := head :: collected -- add new unique element to our tracking list
          let collected_count' := collected_count + 1
          if collected_count' == k then
            ops' -- found all k distinct required numbers
          else
            loop tail collected' collected_count' ops' -- continue searching, count increased
      else
        -- element is irrelevant (> k), zero/negative, or a duplicate (already in `collected`)
        loop tail collected collected_count ops' -- continue searching, count not increased
  -- start the loop, initially empty collection, 0 count, 0 operations
  loop nums.reverse [] 0 0
end RPOrig

namespace RPRef

def minOperations (nums : List Nat) (k : Nat) (h_precond : minOperations_precond (nums) (k)) : Nat :=
  let __rp_tmp_0ae731bc : Nat :=
    -- edge case k=0, requires 0 operations
    if k == 0 then 0 else
    -- recursive helper function
    let rec loop (remaining : List Nat) (collected : List Nat) (collected_count : Nat) (ops : Nat) : Nat :=
      match remaining with
      | [] => ops -- base case
      | head :: tail =>
        let ops' := ops + 1
        -- check if the element is relevant (1 <= head <= k) and not already collected
        -- use a list `collected` to keep track of unique numbers found so far
        if head > 0 && head <= k && !(List.elem head collected) then
            let collected' := head :: collected -- add new unique element to our tracking list
            let collected_count' := collected_count + 1
            if collected_count' == k then
              ops' -- found all k distinct required numbers
            else
              loop tail collected' collected_count' ops' -- continue searching, count increased
        else
          -- element is irrelevant (> k), zero/negative, or a duplicate (already in `collected`)
          loop tail collected collected_count ops' -- continue searching, count not increased
    -- start the loop, initially empty collection, 0 count, 0 operations
    loop nums.reverse [] 0 0
  __rp_tmp_0ae731bc
end RPRef

set_option maxHeartbeats 400000

theorem rp_equiv_rfl (nums : List Nat) (k : Nat) (h_precond : minOperations_precond (nums) (k)) :
    RPOrig.minOperations nums k h_precond = RPRef.minOperations nums k h_precond := rfl

set_option smartUnfolding false in
theorem rp_equiv_rfl_nosmart (nums : List Nat) (k : Nat) (h_precond : minOperations_precond (nums) (k)) :
    RPOrig.minOperations nums k h_precond = RPRef.minOperations nums k h_precond := rfl

theorem rp_equiv_delta_rfl (nums : List Nat) (k : Nat) (h_precond : minOperations_precond (nums) (k)) :
    RPOrig.minOperations nums k h_precond = RPRef.minOperations nums k h_precond := by
  delta RPOrig.minOperations RPRef.minOperations RPOrig.minOperations.loop RPRef.minOperations.loop
  rfl

theorem rp_equiv_simp_only (nums : List Nat) (k : Nat) (h_precond : minOperations_precond (nums) (k)) :
    RPOrig.minOperations nums k h_precond = RPRef.minOperations nums k h_precond := by
  (simp only [RPOrig.minOperations, RPRef.minOperations]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minOperations RPRef.minOperations RPOrig.minOperations.loop RPRef.minOperations.loop; rfl))

theorem rp_equiv_simp (nums : List Nat) (k : Nat) (h_precond : minOperations_precond (nums) (k)) :
    RPOrig.minOperations nums k h_precond = RPRef.minOperations nums k h_precond := by
  (simp [RPOrig.minOperations, RPRef.minOperations]) <;> (first | rfl | (set_option smartUnfolding false in rfl) | (delta RPOrig.minOperations RPRef.minOperations RPOrig.minOperations.loop RPRef.minOperations.loop; rfl))
