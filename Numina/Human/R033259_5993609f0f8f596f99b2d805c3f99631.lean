import Mathlib

theorem algebra_101964 (a b : ℝ) (h₀ : a = b - 1) (h₁ : 1 ≤ b ∧ b ≤ 3) :
    Real.sqrt (a^2 + b^2 - 2 * b + 1) +
    Real.sqrt (a^2 + b^2 - 4 * a - 6 * b + 13) = 2 * Real.sqrt 2 := by
        have h2 : a^2 + b^2 - 2 * b + 1 = 2 * (b - 1) ^ 2 := by
            rw [h₀]
            ring
        have h3 : a^2 + b^2 - 4 * a - 6 * b + 13 = 2 * (b - 3) ^ 2 := by
            rw [h₀]
            ring
        rw [h2, h3]
        have h4 : Real.sqrt (2 * (b - 1) ^ 2) = Real.sqrt 2 * |b - 1| := by
            rw [Real.sqrt_mul (by norm_num)]
            rw [Real.sqrt_sq_eq_abs]
        have h5 : Real.sqrt (2 * (b - 3) ^ 2) = Real.sqrt 2 * |b - 3| := by
            rw [Real.sqrt_mul (by norm_num)]
            rw [Real.sqrt_sq_eq_abs]
        rw [h4, h5]
        have h6 : |b - 1| = b - 1 := by
            rw [abs_of_nonneg]
            linarith [h₁.left]
        have h7 : |b - 3| = 3 - b := by
            rw [abs_of_nonpos]
            linarith [h₁.right]
            all_goals linarith
        rw [h6, h7]
        linarith [Real.sqrt_nonneg 2]