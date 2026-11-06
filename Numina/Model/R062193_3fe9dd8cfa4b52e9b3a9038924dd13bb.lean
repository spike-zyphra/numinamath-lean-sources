import Mathlib

open Real

theorem algebra_2731 : (sqrt 2 + sqrt 5 - sqrt 3) / (2 * sqrt 30 - 6 * sqrt 2 + 4 * sqrt 3) = sqrt 6 / 12 := by
  have h1 : 2 * sqrt 30 - 6 * sqrt 2 + 4 * sqrt 3 = 2 * (sqrt 2 + sqrt 5 - sqrt 3) * sqrt 6 := by
    have h2 : sqrt 30 = sqrt 5 * sqrt 6 := by
      calc
        sqrt 30 = sqrt (5 * 6) := by norm_num
        _ = sqrt 5 * sqrt 6 := by rw [Real.sqrt_mul (by norm_num)]
    have h3 : sqrt 6 = sqrt 2 * sqrt 3 := by
      calc
        sqrt 6 = sqrt (2 * 3) := by norm_num
        _ = sqrt 2 * sqrt 3 := by rw [Real.sqrt_mul (by norm_num)]
    rw [h2]
    rw [h3]
    ring_nf
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), 
      Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
    ]
  have h4 : (sqrt 2 + sqrt 5 - sqrt 3) ≠ 0 := by
    by_contra h
    have h5 : sqrt 2 + sqrt 5 = sqrt 3 := by linarith
    have h6 : sqrt 3 < sqrt 2 + sqrt 5 := by
      have h7 : (sqrt 3) ^ 2 < (sqrt 2 + sqrt 5) ^ 2 := by
        have h8 : (sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
        have h9 : (sqrt 2 + sqrt 5) ^ 2 = (sqrt 2) ^ 2 + (sqrt 5) ^ 2 + 2 * (sqrt 2 * sqrt 5) := by ring
        have h10 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        have h11 : (sqrt 5) ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
        have h12 : sqrt 2 * sqrt 5 = sqrt 10 := by
          calc
            sqrt 2 * sqrt 5 = sqrt (2 * 5) := by rw [Real.sqrt_mul (by norm_num)]
            _ = sqrt 10 := by norm_num
        rw [h8, h9, h10, h11, h12]
        nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)]
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 5]
    linarith [h5, h6]
  rw [h1]
  field_simp [h4]
  <;> ring_nf <;> nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), 
    Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  ]