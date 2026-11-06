import Mathlib

theorem inequalities_201133 (x y : ℝ) (hx : 2 < x) (hy : 2 < y) :
    (x ^ 2 - x) / (y ^ 2 + y) + (y ^ 2 - y) / (x ^ 2 + x) > 2 / 3 := by
  have h1 : 0 < y ^ 2 + y := by
    nlinarith
  have h2 : 0 < x ^ 2 + x := by
    nlinarith
  have h3 : (x ^ 2 - x) / (y ^ 2 + y) + (y ^ 2 - y) / (x ^ 2 + x) - 2 / 3 > 0 := by
    have pos1 : 0 < (y ^ 2 + y) * (x ^ 2 + x) := by positivity
    have h4 : (x ^ 2 - x) / (y ^ 2 + y) + (y ^ 2 - y) / (x ^ 2 + x) - 2 / 3 =
        (3 * ((x ^ 2 - x) * (x ^ 2 + x) + (y ^ 2 - y) * (y ^ 2 + y)) - 2 * ((y ^ 2 + y) * (x ^ 2 + x)) ) / (3 * ((y ^ 2 + y) * (x ^ 2 + x))) := by
      field_simp
      ring
    rw [h4] at *
    apply div_pos
    nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (y^2 - 4), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x - y), sq_nonneg (x * y - 4),
      mul_pos (show (0 : ℝ) < x - 2 by linarith) (show (0 : ℝ) < y - 2 by linarith),
      sq_nonneg (x^2 - y^2), sq_nonneg (x - 2), sq_nonneg (y - 2),
      mul_pos (show (0 : ℝ) < x by linarith) (show (0 : ℝ) < y by linarith)
    ]
    all_goals positivity
  linarith