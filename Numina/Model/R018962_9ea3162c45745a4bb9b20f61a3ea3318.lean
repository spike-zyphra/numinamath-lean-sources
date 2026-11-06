import Mathlib

theorem algebra_297730 : Real.sqrt (2 * (6 - 2 * Real.sqrt 3 - 2 * Real.sqrt 5 + Real.sqrt 15)) = Real.sqrt 3 + Real.sqrt 5 - 2 := by 
  have h1 : (Real.sqrt 3 + Real.sqrt 5 - 2 : ℝ) ≥ 0 := by
    have h2 : Real.sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
    have h3 : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), 
      sq_nonneg (Real.sqrt 3 - 1), sq_nonneg (Real.sqrt 5 - 1),
      Real.sqrt_nonneg 3, Real.sqrt_nonneg 5,
      mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 5),
      Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 5 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have h2 : (Real.sqrt 3 + Real.sqrt 5 - 2 : ℝ) ^ 2 = 2 * (6 - 2 * Real.sqrt 3 - 2 * Real.sqrt 5 + Real.sqrt 15) := by
    have h3 : Real.sqrt 15 = Real.sqrt 3 * Real.sqrt 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    rw [h3]
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, 
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
      sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (Real.sqrt 5 ^ 2 - 5),
      mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 5),
      sq_nonneg (Real.sqrt 3 - Real.sqrt 5)
      ]
  have h4 : 2 * (6 - 2 * Real.sqrt 3 - 2 * Real.sqrt 5 + Real.sqrt 15) = (Real.sqrt 3 + Real.sqrt 5 - 2) ^ 2 := by
    linarith [h2]
  rw [h4]
  rw [Real.sqrt_sq (show (0 : ℝ) ≤ Real.sqrt 3 + Real.sqrt 5 - 2 by linarith [h1] ) ]