import Mathlib

open Real

theorem inequalities_115826 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x * y + 2 * y * z + 2 * z * x) / (x ^ 2 + y ^ 2 + z ^ 2) ≤
    ((1 / 4) * (sqrt 33 + 1)) := by
  have h1 : 0 < x ^ 2 + y ^ 2 + z ^ 2 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]

  have h2 : (x * y + 2 * y * z + 2 * z * x) ≤ (1 / 4) * (sqrt 33 + 1) * (x ^ 2 + y ^ 2 + z ^ 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - (sqrt 33 + 1) / 8 * z), sq_nonneg (y - (sqrt 33 + 1) / 8 * z),
      sq_nonneg (x - (sqrt 33 + 1) / 8 * y), sq_nonneg (z - (sqrt 33 + 1) / 8 * x), 
      Real.sqrt_nonneg 33, Real.sq_sqrt (show 0 ≤ (33 : ℝ) by norm_num),
      mul_nonneg (Real.sqrt_nonneg 33) (Real.sqrt_nonneg 33)
    ]
  have h3 : (x * y + 2 * y * z + 2 * z * x) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ (1 / 4) * (sqrt 33 + 1) := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  linarith