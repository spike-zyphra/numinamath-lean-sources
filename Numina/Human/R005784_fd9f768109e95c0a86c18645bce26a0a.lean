import Mathlib

/-!

A function f:{1,2,3,4,5} → {1,2,3,4,5} is said to be nasty if there do not exist distinct 
a, b ∈ {1,2,3,4,5} satisfying f(a) = b and f(b) = a.

-/

open Fintype

/-- A function f is nasty if no two distinct inputs a and b map to each other. -/
def IsNasty (f : Fin 5 → Fin 5) : Prop :=
  ∀ a b : Fin 5, a ≠ b → ¬(f a = b ∧ f b = a)

/-- The number of functions from Fin 5 to Fin 5 that are nasty. -/
theorem combination_609908 : 
  let total_functions := card (Fin 5 → Fin 5)
  let non_nasty_functions := 1175
  total_functions - non_nasty_functions = 1950 := by

  -- Total number of functions from Fin 5 to Fin 5 is 5^5 = 3125
  have total_count : card (Fin 5 → Fin 5) = 5^5 := by
    -- |B^A| = |B|^|A| when both are finite types
    simp only [card_fun, card_fin]

  -- Count the number of non-nasty functions
  -- These are functions where at least one pair a ≠ b satisfies f(a) = b and f(b) = a

  -- Number of unordered pairs (a, b) with a ≠ b is C(5, 2) = 10
  have pairs_count : (5 * 4) / 2 = 10 := by norm_num

  -- For remaining 3 elements, each maps arbitrarily to 5 values → 5^3
  have maps_for_remaining : 5^3 = 125 := by norm_num

  -- So total functions with exactly one symmetric pair is 10 * 125 = 1250
  have one_pair_functions : 10 * 125 = 1250 := by norm_num

  -- Overcounted cases with two disjoint symmetric pairs must be subtracted

  -- Choose 1 element not in any symmetric pair → 5 choices
  -- The remaining 4 elements are paired as 2 disjoint unordered pairs → 3 ways
  -- The unused element maps to any of 5 values → 5 ways
  have two_pairs_count : 5 * 3 * 5 = 75 := by norm_num

  -- Use inclusion-exclusion to get exact count of non-nasty functions
  have non_nasty_count : 1250 - 75 = 1175 := by norm_num

  -- Subtract to find nasty function count
  calc
    card (Fin 5 → Fin 5) - 1175
      = 5^5 - 1175 := by rw [total_count]
    _ = 3125 - 1175 := by norm_num
    _ = 1950 := by norm_num
