import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_141773 (ε : ℝ) (hε : ε > 0) :
  ∃ δ, δ > 0 ∧ ∀ x, (|x - 5| < δ ∧ x ≠ 5) → |(5 * x ^ 2 - 24 * x - 5) / (x - 5) - 26| < ε := by
  use ε / 5
  constructor
  · -- Show ε / 5 > 0
    linarith
  · -- Show that for all x, if |x - 5| < δ and x ≠ 5, then |(5 * x ^ 2 - 24 * x - 5) / (x - 5) - 26| < ε
    intro x h
    rcases h with ⟨h1, h2⟩
    have h3 : x - 5 ≠ 0 := by
      intro h
      apply h2
      linarith
    have h4 : (5 * x ^ 2 - 24 * x - 5) / (x - 5) = 5 * x + 1 := by
      have h5 : x - 5 ≠ 0 := h3
      field_simp [h5]
      ring
    rw [h4]
    have h7 : |(5 * x + 1) - 26| = 5 * |x - 5| := by
      calc
        |(5 * x + 1) - 26| = |5 * (x - 5)| := by ring_nf
        _ = 5 * |x - 5| := by simp [abs_mul]
    rw [show |(5 * x + 1) - 26| = 5 * |x - 5| by linarith [h7]]
    linarith [abs_lt.mp h1]