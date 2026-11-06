import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_307842 {f : ℝ → ℝ} (h₁ : ∀ x, f (1 + x) = f (1 - x)) (h₂ : ∀ x, f (3 + x) = f (3 - x)) :
    ∀ x, f (4 + x) = f x := by

  have h3 : ∀ y, f y = f (2 - y) := by
    intro y
    have h4 := h₁ (y - 1)
    rw [show 1 + (y - 1 : ℝ) = y by ring, show 1 - (y - 1 : ℝ) = 2 - y by ring] at h4
    linarith [h4]

  have h4 : ∀ z, f z = f (6 - z) := by
    intro z
    have h5 := h₂ (z - 3)
    rw [show 3 + (z - 3 : ℝ) = z by ring, show 3 - (z - 3 : ℝ) = 6 - z by ring] at h5
    linarith [h5]

  intro x
  have h5 : f x = f (2 - x) := h3 x
  have h6 : f (2 - x) = f (4 + x) := by
    have : f (2 - x) = f (6 - (2 - x)) := by
      apply h4
    rw [this]
    ring_nf

  linarith [h5, h6]