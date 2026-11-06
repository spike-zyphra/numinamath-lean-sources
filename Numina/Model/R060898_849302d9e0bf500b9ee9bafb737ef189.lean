import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_141161 (ε : ℝ) (hε : ε > 0) :
  ∃ δ, δ > 0 ∧ ∀ x, (|x + 7 / 2| < δ ∧ x ≠ -7 / 2) → |(2 * x ^ 2 + 13 * x + 21) / (2 * x + 7) + 1 / 2| < ε := by

  use ε
  constructor
  · exact hε

  · intro x h
    have h1 : |x + 7 / 2| < ε := h.1
    have h2 : x ≠ -7 / 2 := h.2
    have h3 : (2 * x ^ 2 + 13 * x + 21) / (2 * x + 7) = x + 3 := by
      have h4 : 2 * x + 7 ≠ 0 := by
        intro h5
        apply h2
        linarith
      field_simp [h4]
      ring
    rw [h3]
    have h5 : |(x + 3) + 1 / 2| = |x + 7 / 2| := by
      have h6 : (x + 3) + 1 / 2 = x + 7 / 2 := by ring
      rw [h6]
    rw [h5]
    exact h1