import Mathlib

theorem algebra_153359 (a b c d : ℝ) (h₀ : a ≥ b) (h₁ : b ≥ c) (h₂ : c ≥ d)
    (h₃ : d ≥ 0) (h₄ : a^2 + d^2 = 1) (h₅ : b^2 + c^2 = 1) (h₆ : a * c + b * d = 1 / 3) :
    a * b - c * d = 2 * √2 / 3 := by
  have h7 : (a * b - c * d) ^ 2 = 8 / 9 := by
    nlinarith [sq_nonneg (a * d - b * c)]
  have h8 : a * b ≥ c * d := by
    nlinarith [mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ b - c by linarith),
          mul_nonneg (show 0 ≤ b - c by linarith) (show 0 ≤ c - d by linarith),
          sq_nonneg (a - c), sq_nonneg (b - d)]
  have h9 : a * b - c * d ≥ 0 := by linarith [h8]
  have h10 : a * b - c * d = 2 * √2 / 3 := by
    have h11 : (a * b - c * d) ^ 2 - 8 / 9 = 0 := by linarith
    have h12 : (a * b - c * d - 2 * √2 / 3) * (a * b - c * d + 2 * √2 / 3) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    cases' (mul_eq_zero.mp h12) with h13 h14
    · -- Case where $(a * b - c * d - 2 * √2 / 3) = 0$
      linarith
    · -- Case where $(a * b - c * d + 2 * √2 / 3) = 0$
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  linarith [h10, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]