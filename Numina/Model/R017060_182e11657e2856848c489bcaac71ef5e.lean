import Mathlib

theorem algebra_3270 {a b c : ℝ} (habc : a * b * c = 8) (hab : a * b + 2 * a + 4 ≠ 0) (hbc : b * c + 2 * b + 4 ≠ 0) (hca : c * a + 2 * c + 4 ≠ 0) :
    2 * a / (a * b + 2 * a + 4) + 2 * b / (b * c + 2 * b + 4) + 2 * c / (c * a + 2 * c + 4) = 1 := by
  field_simp [(show a * b + 2 * a + 4 ≠ 0 by exact hab), (show b * c + 2 * b + 4 ≠ 0 by exact hbc), (show c * a + 2 * c + 4 ≠ 0 by exact hca)]
  nlinarith [sq_nonneg (a * b - 4), sq_nonneg (b * c - 4), sq_nonneg (c * a - 4), sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2), sq_nonneg (a * b + b * c + c * a - 12), sq_nonneg (a * b * c - 8)]