import Mathlib

theorem inequalities_48112 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    2 ≤ (x ^ 9 + y ^ 9) / (x ^ 6 + x ^ 3 * y ^ 3 + y ^ 6) +
        (x ^ 9 + z ^ 9) / (x ^ 6 + x ^ 3 * z ^ 3 + z ^ 6) +
        (y ^ 9 + z ^ 9) / (y ^ 6 + y ^ 3 * z ^ 3 + z ^ 6) := by

  have h1 : 0 < x ^ 3 := by positivity
  have h2 : 0 < y ^ 3 := by positivity
  have h3 : 0 < z ^ 3 := by positivity
  have h4 : x ^ 3 * y ^ 3 * z ^ 3 = 1 := by
    have h5 : x ^ 3 * y ^ 3 * z ^ 3 = (x * y * z) ^ 3 := by ring
    rw [h5, hxyz]
    all_goals norm_num

  have h5 : (x ^ 9 + y ^ 9) / (x ^ 6 + x ^ 3 * y ^ 3 + y ^ 6) ≥ (x ^ 3 + y ^ 3) / 3 := by
    have h6 : 0 < x ^ 6 + x ^ 3 * y ^ 3 + y ^ 6 := by positivity
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 3 * (x ^ 3 - y ^ 3)), sq_nonneg (y ^ 3 * (y ^ 3 - x ^ 3)), sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 3 + y ^ 3), mul_pos (show 0 < x ^ 3 by positivity) (show 0 < y ^ 3 by positivity)]

  have h6 : (x ^ 9 + z ^ 9) / (x ^ 6 + x ^ 3 * z ^ 3 + z ^ 6) ≥ (x ^ 3 + z ^ 3) / 3 := by
    have h7 : 0 < x ^ 6 + x ^ 3 * z ^ 3 + z ^ 6 := by positivity
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (x ^ 3 - z ^ 3), sq_nonneg (x ^ 3 - z ^ 3), sq_nonneg (x ^ 3 * (x ^ 3 - z ^ 3)), sq_nonneg (z ^ 3 * (z ^ 3 - x ^ 3)), sq_nonneg (x ^ 3 - z ^ 3), sq_nonneg (x ^ 3 + z ^ 3), mul_pos (show 0 < x ^ 3 by positivity) (show 0 < z ^ 3 by positivity)]

  have h7 : (y ^ 9 + z ^ 9) / (y ^ 6 + y ^ 3 * z ^ 3 + z ^ 6) ≥ (y ^ 3 + z ^ 3) / 3 := by
    have h8 : 0 < y ^ 6 + y ^ 3 * z ^ 3 + z ^ 6 := by positivity
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (y ^ 3 - z ^ 3), sq_nonneg (y ^ 3 - z ^ 3), sq_nonneg (y ^ 3 * (y ^ 3 - z ^ 3)), sq_nonneg (z ^ 3 * (z ^ 3 - y ^ 3)), sq_nonneg (y ^ 3 - z ^ 3), sq_nonneg (y ^ 3 + z ^ 3), mul_pos (show 0 < y ^ 3 by positivity) (show 0 < z ^ 3 by positivity)]

  have h8 : x ^ 3 + y ^ 3 + z ^ 3 ≥ 3 := by
    nlinarith [sq_nonneg (x ^ 3 - 1), sq_nonneg (y ^ 3 - 1), sq_nonneg (z ^ 3 - 1),
      mul_pos (show 0 < x ^ 3 by positivity) (show 0 < y ^ 3 by positivity),
      mul_pos (show 0 < y ^ 3 by positivity) (show 0 < z ^ 3 by positivity),
      mul_pos (show 0 < x ^ 3 by positivity) (show 0 < z ^ 3 by positivity),
      h4
    ]
  have h9 : (x ^ 3 + y ^ 3) / 3 + (y ^ 3 + z ^ 3) / 3 + (x ^ 3 + z ^ 3) / 3 ≥ 2 := by
    nlinarith [h8]

  have h10 : (x ^ 9 + y ^ 9) / (x ^ 6 + x ^ 3 * y ^ 3 + y ^ 6) + (x ^ 9 + z ^ 9) / (x ^ 6 + x ^ 3 * z ^ 3 + z ^ 6) + (y ^ 9 + z ^ 9) / (y ^ 6 + y ^ 3 * z ^ 3 + z ^ 6) ≥ (x ^ 3 + y ^ 3) / 3 + (y ^ 3 + z ^ 3) / 3 + (x ^ 3 + z ^ 3) / 3 := by
    linarith [h5, h6, h7]

  linarith [h10, h9]