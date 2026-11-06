import Mathlib

theorem algebra_300145 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 = 49) (h2 : y^2 + y * z + z^2 = 36) (h3 : z^2 + z * x + x^2 = 25) :
    x + y + z = Real.sqrt (55 + 36 * Real.sqrt 2) := by

  have h41 : (x + y + z) ^ 2 = 55 + 36 * Real.sqrt 2 := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
    ]

  have h51 : 0 ≤ (55 + 36 * Real.sqrt 2 : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  have h61 : x + y + z ≥ 0 := by
    linarith

  have h71 : (x + y + z : ℝ) = Real.sqrt (55 + 36 * Real.sqrt 2) := by
    have h81 : (x + y + z : ℝ) ^ 2 = 55 + 36 * Real.sqrt 2 := h41
    have h91 : (x + y + z : ℝ) ≥ 0 := h61
    have h101 : Real.sqrt (55 + 36 * Real.sqrt 2) ≥ 0 := by 
      apply Real.sqrt_nonneg
    have h111 : (Real.sqrt (55 + 36 * Real.sqrt 2 : ℝ)) ^ 2 = 55 + 36 * Real.sqrt 2 := by 
      rw [Real.sq_sqrt]
      linarith [h51]
    nlinarith [Real.sqrt_nonneg (55 + 36 * Real.sqrt 2)]
  exact h71