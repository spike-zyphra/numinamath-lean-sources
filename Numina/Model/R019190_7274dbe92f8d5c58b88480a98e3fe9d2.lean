import Mathlib

open Real

theorem algebra_302906 : sqrt (5 - sqrt 24) / (sqrt 10 + 3 - sqrt 6 - sqrt 15) =
    -1 / 2 * (sqrt 5 + sqrt 3) := by 
  have h1 : sqrt 24 = 2 * sqrt 6 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    <;> ring_nf 
    <;> norm_num 
  have h2 : 5 - sqrt 24 = 5 - 2 * sqrt 6 := by 
    rw [h1]
  have h2a : sqrt (5 - sqrt 24) = sqrt (5 - 2 * sqrt 6) := by
    rw [h2]
  have h5 : sqrt (5 - 2 * sqrt 6) = sqrt 3 - sqrt 2 := by
    have h12 : sqrt 6 = sqrt 2 * sqrt 3 := by
      have h23 : (6 : ℝ) = (2 : ℝ) * (3 : ℝ) := by norm_num
      rw [h23]
      field_simp [Real.sqrt_mul_self]
      <;> ring_nf
      <;> norm_num
    rw [h12]
    have h6 : (sqrt 3 - sqrt 2) ^ 2 = 5 - 2 * (sqrt 2 * sqrt 3) := by 
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, sq_nonneg (sqrt 3 ^ 2 - 2), sq_nonneg (sqrt 2 ^ 2 - 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (2 : ℝ), 
          Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h7 : sqrt (5 - 2 * (sqrt 2 * sqrt 3)) = sqrt 3 - sqrt 2 := by 
      have h8 : 5 - 2 * (sqrt 2 * sqrt 3) = (sqrt 3 - sqrt 2) ^ 2 := by 
        nlinarith [h6]
      rw [h8]
      have h9 : 0 ≤ (sqrt 3 - sqrt 2 : ℝ) := by 
        have h1234 : sqrt 2 < sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg (2), Real.sqrt_nonneg (3)]
      rw [Real.sqrt_sq (by 
        linarith 
      )]
    linarith
  have h10 : sqrt (5 - sqrt 24) = sqrt 3 - sqrt 2 := by 
    rw [h2a]
    rw [h5]
  have h8 : sqrt (10 : ℝ) = sqrt 2 * sqrt 5 := by 
    have h100 : (10 : ℝ) = (2 : ℝ) * (5 : ℝ) := by norm_num
    rw [h100]
    field_simp [Real.sqrt_mul_self]
  have h9 : sqrt (6 : ℝ) = sqrt 2 * sqrt 3 := by
    have h100 : (6 : ℝ) = (2 : ℝ) * (3 : ℝ) := by norm_num 
    rw [h100]
    field_simp [Real.sqrt_mul_self]
  have h100 : sqrt (15 : ℝ) = sqrt 3 * sqrt 5 := by 
    have h100 : (15 : ℝ) = (3 : ℝ) * (5 : ℝ) := by norm_num 
    rw [h100]
    field_simp [Real.sqrt_mul_self]
  rw [h10]
  rw [h8, h9, h100]
  field_simp [(show sqrt 2 * sqrt 5 + 3 - sqrt 2 * sqrt 3 - sqrt 3 * sqrt 5 ≠ 0 by 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), 
        sq_nonneg (sqrt 2 - sqrt 3), sq_nonneg (sqrt 2 - sqrt 5), sq_nonneg (sqrt 3 - sqrt 5), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
        Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (5 : ℝ), 
        mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (3 : ℝ)), 
        mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (5 : ℝ)), 
        mul_nonneg (Real.sqrt_nonneg (3 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))
      ]
  )
  ]
  <;> nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (5 : ℝ), 
      sq_nonneg (sqrt 2 - sqrt 3), sq_nonneg (sqrt 2 - sqrt 5), sq_nonneg (sqrt 3 - sqrt 5), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
      Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (5 : ℝ), 
      mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (3 : ℝ)), 
      mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (Real.sqrt_nonneg (5 : ℝ)), 
      mul_nonneg (Real.sqrt_nonneg (3 : ℝ)) (Real.sqrt_nonneg (5 : ℝ))
    ]