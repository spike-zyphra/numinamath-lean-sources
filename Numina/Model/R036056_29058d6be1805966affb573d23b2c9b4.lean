import Mathlib

theorem inequalities_153306 (a b x y : ℝ) : (a^2 + b^2) * (x^2 + y^2) ≥ |a * x + b * y| * |b * x + a * y| := by
  have h1 : |a * x + b * y| * |b * x + a * y| = |(a * x + b * y) * (b * x + a * y)| := by
    rw [← abs_mul]
  rw [h1]
  have h2 : (a^2 + b^2) * (x^2 + y^2) ≥ |(a * x + b * y) * (b * x + a * y)| := by
    have h3 : - (a^2 + b^2) * (x^2 + y^2) ≤ (a * x + b * y) * (b * x + a * y) := by
      nlinarith [sq_nonneg (a * y - b * x), sq_nonneg (a * x - b * y), sq_nonneg (a * x + b * y - (b * x + a * y)), sq_nonneg (a - b), sq_nonneg (x - y), sq_nonneg (a * x + b * y + (b * x + a * y)), sq_nonneg ((a^2 + b^2) - (x^2 + y^2)), sq_nonneg (a * x - b * y), sq_nonneg (a * y - b * x)]
    have h4 : (a * x + b * y) * (b * x + a * y) ≤ (a^2 + b^2) * (x^2 + y^2) := by
      nlinarith [sq_nonneg (a * y - b * x), sq_nonneg (a * x - b * y), sq_nonneg (a * x + b * y - (b * x + a * y)), sq_nonneg (a - b), sq_nonneg (x - y), sq_nonneg (a * x + b * y + (b * x + a * y)), sq_nonneg ((a^2 + b^2) - (x^2 + y^2)), sq_nonneg (a * x - b * y), sq_nonneg (a * y - b * x)]
    apply abs_le.mpr
    constructor <;> nlinarith
  linarith