-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux
def toLower (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then
    Char.ofNat (Char.toNat c + 32)
  else
    c

def normalize_str (s : String) : List Char :=
  s.data.map toLower
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def allVowels_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def allVowels__rp_helper_1905f5d2 (s : String) (h_precond : allVowels_precond (s)) : Bool :=
  let chars := normalize_str s
  let vowelSet := ['a', 'e', 'i', 'o', 'u']
  vowelSet.all (fun v => chars.contains v)
-- !benchmark @end code_aux


def allVowels (s : String) (h_precond : allVowels_precond (s)) : Bool :=
  -- !benchmark @start code
  allVowels__rp_helper_1905f5d2 s h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def allVowels_postcond (s : String) (result: Bool) (h_precond : allVowels_precond (s)) : Prop :=
  -- !benchmark @start postcond
  let chars := normalize_str s
  (result ↔ List.all ['a', 'e', 'i', 'o', 'u'] (fun v => chars.contains v))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem allVowels_spec_satisfied (s: String) (h_precond : allVowels_precond (s)) :
    allVowels_postcond (s) (allVowels (s) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : (allVowels s h_precond = true) ↔ List.all ['a', 'e', 'i', 'o', 'u'] (fun v => v ∈ (normalize_str s)) := by
    dsimp only [allVowels]
    have h₁ : (List.all ['a', 'e', 'i', 'o', 'u'] (fun v => (normalize_str s).contains v) = true) ↔ List.all ['a', 'e', 'i', 'o', 'u'] (fun v => v ∈ (normalize_str s)) := by
      -- Use the fact that the list is nonempty and the predicates are equivalent for each element
      simp only [List.all_cons, List.all_nil, true_and]
      -- Use a decision procedure to verify the equivalence for each case
      <;>
      (try decide) <;>
      (try
        {
          simp [List.contains_cons, List.mem_cons, List.mem_nil_iff, or_false_iff]
          <;>
          (try decide) <;>
          (try
            {
              cases (normalize_str s).contains 'a' <;>
              cases (normalize_str s).contains 'e' <;>
              cases (normalize_str s).contains 'i' <;>
              cases (normalize_str s).contains 'o' <;>
              cases (normalize_str s).contains 'u' <;>
              simp_all [List.contains_cons, List.mem_cons, List.mem_nil_iff, or_false_iff] <;>
              (try decide)
            }
          )
        }
      )
      <;>
      (try
        {
          simp_all [List.contains_cons, List.mem_cons, List.mem_nil_iff, or_false_iff]
          <;>
          (try decide)
        }
      )
      <;>
      (try
        {
          aesop
        }
      )
    -- Convert the result to the desired form
    simpa [h₁] using h₁

  dsimp only [allVowels_postcond] at *
  simp_all [allVowels_precond]
  <;>
  (try simp_all) <;>
  (try tauto) <;>
  (try aesop)
  -- !benchmark @end proof


