import Mathlib

theorem inequalities_598763 (x y z : ℝ) :
    (x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) + (y ^ 2 - z ^ 2) / (2 * y ^ 2 + 1) +
    (z ^ 2 - x ^ 2) / (2 * z ^ 2 + 1) ≤ 0 := by
  have h1 : 0 < (2 * x ^ 2 + 1 : ℝ) := by nlinarith [sq_nonneg x]
  have h2 : 0 < (2 * y ^ 2 + 1 : ℝ) := by nlinarith [sq_nonneg y]
  have h3 : 0 < (2 * z ^ 2 + 1 : ℝ) := by nlinarith [sq_nonneg z]
  have h5 : (x ^ 2 - y ^ 2) / (2 * x ^ 2 + 1) + (y ^ 2 - z ^ 2) / (2 * y ^ 2 + 1) + (z ^ 2 - x ^ 2) / (2 * z ^ 2 + 1) =
      ((x ^ 2 - y ^ 2) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1) + (y ^ 2 - z ^ 2) * (2 * x ^ 2 + 1) * (2 * z ^ 2 + 1) + (z ^ 2 - x ^ 2) * (2 * x ^ 2 + 1) * (2 * y ^ 2 + 1)) / ((2 * x ^ 2 + 1) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1)) := by
    field_simp
    ring
  rw [h5] at *
  have h6 : 0 < (2 * x ^ 2 + 1 : ℝ) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1) := by
    positivity
  have h7 : ((x ^ 2 - y ^ 2) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1) + (y ^ 2 - z ^ 2) * (2 * x ^ 2 + 1) * (2 * z ^ 2 + 1) + (z ^ 2 - x ^ 2) * (2 * x ^ 2 + 1) * (2 * y ^ 2 + 1)) ≤ 0 := by
    nlinarith [sq_nonneg (x^2 - 1/2), sq_nonneg (y^2 - 1/2), sq_nonneg (z^2 - 1/2), 
        sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x),
        sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2),
        mul_nonneg (show 0 ≤ x^2 by nlinarith [sq_nonneg x]) (show 0 ≤ y^2 by nlinarith [sq_nonneg y]), 
        mul_nonneg (show 0 ≤ y^2 by nlinarith [sq_nonneg y]) (show 0 ≤ z^2 by nlinarith [sq_nonneg z]), 
        mul_nonneg (show 0 ≤ z^2 by nlinarith [sq_nonneg z]) (show 0 ≤ x^2 by nlinarith [sq_nonneg x])
    ]
  have h8 : ((x ^ 2 - y ^ 2) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1) + (y ^ 2 - z ^ 2) * (2 * x ^ 2 + 1) * (2 * z ^ 2 + 1) + (z ^ 2 - x ^ 2) * (2 * x ^ 2 + 1) * (2 * y ^ 2 + 1)) / ((2 * x ^ 2 + 1) * (2 * y ^ 2 + 1) * (2 * z ^ 2 + 1)) ≤ 0 := by 
    apply div_nonpos_of_nonpos_of_nonneg
    linarith [h7]
    all_goals 
      positivity
  linarith [h8]