import Mathlib

theorem algebra_226067 (a b c d : ℝ) (h₀ : a * b = 1) (h₁ : c ^ 2 + d ^ 2 = 1) :
    (a - c) ^ 2 + (b - d) ^ 2 ≥ 3 - 2 * √2 := by

  have h2 : (a - c) ^ 2 + (b - d) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 - 2 * (a * c + b * d) := by
    nlinarith

  have h3 : c ^ 2 + d ^ 2 = 1 := h₁

  have h4 : (a - c) ^ 2 + (b - d) ^ 2 = a ^ 2 + b ^ 2 + 1 - 2 * (a * c + b * d) := by
    nlinarith [h3, h2]

  have h5 : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a * d - b * c)]

  have h6 : (a * c + b * d) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rw [show c ^ 2 + d ^ 2 = 1 by linarith] at h5
    nlinarith

  have h7 : a ^ 2 + b ^ 2 ≥ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b - 1)]

  have h8 : a ^ 2 + b ^ 2 + 1 - 2 * (a * c + b * d) ≥ 3 - 2 * Real.sqrt 2 := by

    have h9 : (a * c + b * d) ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
      have h10 : (a * c + b * d) ^ 2 ≤ a ^ 2 + b ^ 2 := h6
      have h11 : (a * c + b * d) ≤ Real.sqrt (a ^ 2 + b ^ 2) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      exact h11

    have h11 : a ^ 2 + b ^ 2 + 1 - 2 * (a * c + b * d) ≥ a ^ 2 + b ^ 2 + 1 - 2 * Real.sqrt (a ^ 2 + b ^ 2) := by
      nlinarith [h9]

    have h13 : a ^ 2 + b ^ 2 + 1 - 2 * Real.sqrt (a ^ 2 + b ^ 2) ≥ 3 - 2 * Real.sqrt 2 := by
      have h9 : Real.sqrt (a ^ 2 + b ^ 2) ≥ Real.sqrt (2 : ℝ) := by
        apply Real.sqrt_le_sqrt
        nlinarith [h7]

      have h101 : a ^ 2 + b ^ 2 ≥ (2 : ℝ) := by nlinarith [h7]

      nlinarith [sq_nonneg (Real.sqrt (a ^ 2 + b ^ 2) - Real.sqrt 2), Real.sqrt_nonneg (a ^ 2 + b ^ 2), Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + b ^ 2) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by nlinarith), Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (a ^ 2 + b ^ 2)]

    linarith

  linarith [h4, h8]