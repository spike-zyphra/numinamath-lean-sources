import Mathlib

theorem algebra_248658 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : ∃ s : Finset ℝ, s.card > 0 ∧ ∃ a ∈ s, a = x ^ 2) :
    ∃ s : Finset ℝ, s.card > 0 ∧ ∃ a ∈ s, a = x * y := by
  use {x * y}
  constructor
  · -- Show the cardinality of the singleton set is greater than 0
    simp
  · -- Show that x * y exists in the set {x * y}
    refine ⟨x * y, by simp, rfl⟩