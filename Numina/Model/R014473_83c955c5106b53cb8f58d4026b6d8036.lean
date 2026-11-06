import Mathlib

theorem inequalities_66127 (a b c d : ℝ) (h₀ : b < c) (h₁ : c < d) :
    (a + b + c + d)^2 > 8 * (a * c + b * d) := by
  nlinarith [sq_nonneg (a + d - (b + c)), sq_nonneg (a - c), sq_nonneg (b - d),
            sq_nonneg (c - b), sq_nonneg (d - c),
            mul_pos (sub_pos.mpr h₀) (sub_pos.mpr h₁),
            sq_nonneg (a + b - c - d), sq_nonneg (a - d + (c - b)), sq_nonneg (a + d - (b + c)), sq_nonneg (a - c + (b - d))]