import Mathlib

theorem number_theory_205734 :
    ∃ x y : Finset ℕ,
      x ⊆ {250, 160, 180, 120, 130, 210, 110, 140, 360} ∧
      y ⊆ {250, 160, 180, 120, 130, 210, 110, 140, 360} ∧
      x ≠ y ∧
      ∑ i ∈ x, i = 1000 ∧
      ∑ i ∈ y, i = 1000 := by
  use {130, 360, 210, 180, 120}, {360, 110, 120, 250, 160}
  constructor
  · -- Show that {130, 360, 210, 180, 120} is a subset of the given numbers.
    native_decide
  constructor
  · -- Show that {360, 110, 120, 250, 160} is a subset of the given numbers.
    native_decide
  constructor
  · -- Show that the two sets are different.
    native_decide
  constructor
  · -- Show that the sum of the first set is 1000.
    native_decide
  · -- Show that the sum of the second set is 1000.
    native_decide