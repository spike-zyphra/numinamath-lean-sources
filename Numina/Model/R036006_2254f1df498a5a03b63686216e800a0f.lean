import Mathlib

open Real Set


theorem inequalities_601824
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 1) :
    x / (1 + x^2) + y / (1 + y^2) + z / (1 + z^2) ≤ 3 * sqrt 3 / 4 := by

  have h2 : x / (1 + x^2) ≤ (3 / 8) * x + Real.sqrt 3 / 8 := by
    have h10 : 0 < (1 + x^2 : ℝ) := by positivity
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (x ^ 2 - 1 / 3), sq_nonneg (x - Real.sqrt 3 / 3), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
      sq_nonneg (x ^ 2 - 1 / 3), sq_nonneg (x * (x ^ 2) - (Real.sqrt 3 / 3) * (x ^ 2)), 
      sq_nonneg (x - Real.sqrt 3 / 3), mul_pos hx (show 0 < x by linarith)
      ]

  have h3 : y / (1 + y^2) ≤ (3 / 8) * y + Real.sqrt 3 / 8 := by
    have h10 : 0 < (1 + y^2 : ℝ) := by positivity
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (y ^ 2 - 1 / 3), sq_nonneg (y - Real.sqrt 3 / 3), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
      sq_nonneg (y ^ 2 - 1 / 3), sq_nonneg (y * (y ^ 2) - (Real.sqrt 3 / 3) * (y ^ 2)), 
      sq_nonneg (y - Real.sqrt 3 / 3), mul_pos hy (show 0 < y by linarith)
      ]

  have h4 : z / (1 + z^2) ≤ (3 / 8) * z + Real.sqrt 3 / 8 := by
    have h10 : 0 < (1 + z^2 : ℝ) := by positivity
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [sq_nonneg (z ^ 2 - 1 / 3), sq_nonneg (z - Real.sqrt 3 / 3), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num),
      sq_nonneg (z ^ 2 - 1 / 3), sq_nonneg (z * (z ^ 2) - (Real.sqrt 3 / 3) * (z ^ 2)), 
      sq_nonneg (z - Real.sqrt 3 / 3), mul_pos hz (show 0 < z by linarith)
      ]

  have h7 : x / (1 + x^2) + y / (1 + y^2) + z / (1 + z^2) ≤ (3 / 8) * (x + y + z) + 3 * Real.sqrt 3 / 8 := by
    linarith [h2, h3, h4]

  have h8 : (x + y + z) ^ 2 ≤ 3 * (x^2 + y^2 + z^2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

  have h9 : (x + y + z) ^ 2 ≤ 3 := by
    have h10 : x^2 + y^2 + z^2 = 1 := h
    nlinarith

  have h10 : x + y + z ≤ Real.sqrt 3 := by
    have h11 : (x + y + z) ^ 2 ≤ (3 : ℝ) := h9
    have h12 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    have h13 : 0 ≤ (Real.sqrt 3 : ℝ) := Real.sqrt_nonneg 3
    nlinarith [Real.sqrt_nonneg 3]

  nlinarith [h7, h10, Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        ]