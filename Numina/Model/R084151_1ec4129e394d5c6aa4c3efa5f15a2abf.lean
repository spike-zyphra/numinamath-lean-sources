import Mathlib

theorem algebra_268671 (S : Finset ℕ) (hS : S = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}) :
    (S \ {5}).card = 10 ∧ ∑ x ∈ (S \ {5}), x = 61 := by
  rw [hS]
  constructor
  · -- Show that the cardinality is 10
    native_decide
  · -- Show that the sum is 61
    native_decide