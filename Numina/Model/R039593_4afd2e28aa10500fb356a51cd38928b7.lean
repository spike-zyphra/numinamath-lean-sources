import Mathlib

theorem algebra_307131 (m : ℝ) :
    ∃ x₁ x₂ : ℝ, x₁ ≠ x₂ ∧ x₁^2 + (1 - m) * x₁ - (1 + m) = 0 ∧
      x₂^2 + (1 - m) * x₂ - (1 + m) = 0 ∧ x₁ < m ∧ x₂ > m := by
  use (m - 1 - Real.sqrt (m ^ 2 + 2 * m + 5)) / 2,
    (m - 1 + Real.sqrt (m ^ 2 + 2 * m + 5)) / 2
  constructor
  · -- Show that x₁ ≠ x₂
    by_contra h
    have h1 : Real.sqrt (m ^ 2 + 2 * m + 5) = 0 := by
      nlinarith [Real.sqrt_nonneg (m ^ 2 + 2 * m + 5)]
    have h2 : Real.sqrt (m ^ 2 + 2 * m + 5) > 0 := by
      apply Real.sqrt_pos.2
      have h3 : m ^ 2 + 2 * m + 5 > 0 := by
        nlinarith [sq_nonneg (m + 1)]
      linarith
    linarith [Real.sqrt_nonneg (m ^ 2 + 2 * m + 5)]
  constructor
  · -- Show that x₁^2 + (1 - m) * x₁ - (1 + m) = 0
    nlinarith [Real.sqrt_nonneg (m ^ 2 + 2 * m + 5),
      Real.sq_sqrt (show 0 ≤ m ^ 2 + 2 * m + 5 by nlinarith [sq_nonneg (m + 1)]) ]
  constructor
  · -- Show that x₂^2 + (1 - m) * x₂ - (1 + m) = 0
    nlinarith [Real.sqrt_nonneg (m ^ 2 + 2 * m + 5),
      Real.sq_sqrt (show 0 ≤ m ^ 2 + 2 * m + 5 by nlinarith [sq_nonneg (m + 1)]) ]
  constructor
  · -- Show that x₁ < m
    nlinarith [Real.sqrt_nonneg (m ^ 2 + 2 * m + 5),
      Real.sq_sqrt (show 0 ≤ m ^ 2 + 2 * m + 5 by nlinarith [sq_nonneg (m + 1)]) ]
  · -- Show that x₂ > m
    nlinarith [Real.sqrt_nonneg (m ^ 2 + 2 * m + 5),
      Real.sq_sqrt (show 0 ≤ m ^ 2 + 2 * m + 5 by nlinarith [sq_nonneg (m + 1)]) ]