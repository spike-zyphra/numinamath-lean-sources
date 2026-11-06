import Mathlib

theorem number_theory_232651 : ∃ s : Finset ℕ, ∑ n ∈ s, n = 231 ∧ ∏ n ∈ s, n = 231 := by
  use {231}
  all_goals
  constructor
  · -- Show that the sum of the elements in s equals 231
    simp
  · -- Show that the product of the elements in s equals 231
    simp