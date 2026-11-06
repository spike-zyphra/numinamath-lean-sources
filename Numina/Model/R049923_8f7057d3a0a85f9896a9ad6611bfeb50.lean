import Mathlib

theorem algebra_163485 {n : ℕ} (hn : n > 0) :
    ∃ s : Finset ℕ, s ⊆ Finset.Icc 1 (n - 1) ∧
      (∀ x ∈ s, x > 0) ∧
      (∏ x ∈ s, (x / (x + 1 : ℚ)) = 1) := by
  use ∅
  constructor
  · -- Show that the empty set is a subset of Finset.Icc 1 (n - 1)
    simp
  constructor
  · -- Show that for all x in the empty set, x > 0 holds (this is trivial)
    simp
  · -- Show that the product over the empty set equals 1
    simp