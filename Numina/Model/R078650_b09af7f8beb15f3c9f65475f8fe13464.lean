import Mathlib

theorem number_theory_284188 (S : Finset ℕ) (hS : S = {2, 3, 5, 7, 11, 13, 17, 19}) :
    ∃ T ⊆ S, T.card = 3 ∧ ∑ x ∈ T, x = ∑ x ∈ S \ T, x + 1 := by
  use {3, 17, 19}
  rw [hS]
  constructor
  · -- Show {3, 17, 19} ⊆ {2, 3, 5, 7, 11, 13, 17, 19}
    native_decide
  constructor
  · -- Show that {3, 17, 19} has cardinality 3
    native_decide
  · -- Show that the sum of {3, 17, 19} is one greater than the sum of the remaining elements
    native_decide