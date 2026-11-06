import Mathlib

theorem algebra_105515 (x y : ℝ) (h : 4*x^2+4*y^2+16*x-12*y+21=0) : |2*x-2*y+7| ≤ 4 := by
  have h1 : (x + 2) ^ 2 + (y - 3 / 2) ^ 2 = 1 := by
    nlinarith
  have h2 : -4 ≤ 2 * x - 2 * y + 7 := by
    nlinarith [sq_nonneg (x + 2 - (y - 3 / 2)), sq_nonneg (x + 2 + (y - 3 / 2)), sq_nonneg ((x + 2) * ((y - 3 / 2))), sq_nonneg ((x + 2 + (y - 3 / 2)))]
  have h3 : 2 * x - 2 * y + 7 ≤ 4 := by
    nlinarith [sq_nonneg (x + 2 - (y - 3 / 2)), sq_nonneg (x + 2 + (y - 3 / 2)), sq_nonneg ((x + 2) * ((y - 3 / 2))), sq_nonneg ((x + 2 + (y - 3 / 2)))]
  apply abs_le.mpr
  constructor <;> linarith