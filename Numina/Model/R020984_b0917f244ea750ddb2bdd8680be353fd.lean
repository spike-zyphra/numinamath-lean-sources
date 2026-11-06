import Mathlib

theorem algebra_315339 (p : ℝ) (x₁ x₂ : ℝ) (h : x₁ ≠ x₂)
    (h₁ : x₁^2 - 2 * p * x₁ - p = 0) (h₂ : x₂^2 - 2 * p * x₂ - p = 0) :
    2 * p * x₁ + x₂^2 + 3 * p > 0 ∧
    (|x₁ - x₂| ≤ |2 * p - 3| → p ≤ 9 / 16) := by

  have h5 : x₁ - x₂ ≠ 0 := by
    intro h'
    apply h
    linarith

  have h7 : x₁ + x₂ = 2 * p := by
    apply (mul_left_inj' h5).mp
    nlinarith

  have h8 : 2 * p * x₁ + x₂^2 + 3 * p > 0 := by
    have h9 : x₂^2 = 2 * p * x₂ + p := by nlinarith
    rw [h9]
    have h10 : 2 * p * x₁ + (2 * p * x₂ + p) + 3 * p = 4 * p ^ 2 + 4 * p := by
      have h11 : x₁ + x₂ = 2 * p := h7
      nlinarith [h11]
    have h12 : 4 * p ^ 2 + 4 * p > 0 := by
      have h13 : x₁^2 - 2 * p * x₁ - p = 0 := h₁
      have h14 : x₂^2 - 2 * p * x₂ - p = 0 := h₂
      nlinarith [sq_pos_of_ne_zero (show x₁ - x₂ ≠ 0 by exact h5), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - 2 * p), sq_nonneg (x₁ * x₂)]
    linarith [h10, h12]

  have h9 : |x₁ - x₂| ≤ |2 * p - 3| → p ≤ 9 / 16 := by
    intro h10
    have h11 : (x₁ - x₂) ^ 2 = 4 * p ^ 2 + 4 * p := by
      have h12 : x₁ + x₂ = 2 * p := h7
      nlinarith [sq_pos_of_ne_zero (show x₁ - x₂ ≠ 0 by exact h5), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂), sq_nonneg (x₁ * x₂)]
    have h14 : (x₁ - x₂) ^ 2 ≤ (2 * p - 3) ^ 2 := by
      apply sq_le_sq.mpr
      simpa using h10
    nlinarith [sq_nonneg (2 * p - 3), sq_nonneg (x₁ - x₂), h11]

  constructor
  · linarith [h8]
  · intro h10
    apply h9 h10