import Mathlib

theorem algebra_158395 (a : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 2 - 2 * x - abs (x - 1 - a) - abs (x - 2) + 4)
    (h₁ : ∀ x, f x ≥ 0) :
    -2 ≤ a ∧ a ≤ 1 := by

  have h2 := h₁ 1
  rw [h₀ 1] at h2

  have h3 : abs (1 - 1 - a) = abs (-a) := by
    ring_nf

  have h4 : abs (1 - 2 : ℝ) = (1 : ℝ) := by
    norm_num [abs_of_neg, abs_of_nonneg]

  rw [h3, h4] at h2

  have h5 : abs (-a) ≤ 2 := by
    linarith

  have h6 := h₁ 0
  rw [h₀ 0] at h6

  have h7 : abs (0 - 1 - a) = abs (-1 - a) := by
    ring_nf

  have h8 : abs (0 - 2 : ℝ) = (2 : ℝ) := by
    norm_num [abs_of_neg, abs_of_nonneg]

  rw [h7, h8] at h6

  have h9 : abs (-1 - a) ≤ 2 := by
    linarith

  have h10 : -2 ≤ a := by 
    cases' abs_le.mp (show abs (-a) ≤ 2 by linarith) with h11 h12
    linarith

  have h11 : a ≤ 1 := by 
    cases' abs_le.mp (show abs (-1 - a) ≤ 2 by linarith) with h12 h13
    linarith

  constructor
  · linarith
  · linarith