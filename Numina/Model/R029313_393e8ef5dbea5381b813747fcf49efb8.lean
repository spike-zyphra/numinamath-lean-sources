import Mathlib

theorem inequalities_140055 : (Real.sqrt 7 + Real.sqrt 10 < Real.sqrt 3 + Real.sqrt 19) := by
  have h1 : Real.sqrt 7 ≥ 0 := Real.sqrt_nonneg 7
  have h2 : Real.sqrt 10 ≥ 0 := Real.sqrt_nonneg 10
  have h3 : Real.sqrt 3 ≥ 0 := Real.sqrt_nonneg 3
  have h4 : Real.sqrt 19 ≥ 0 := Real.sqrt_nonneg 19
  have h5 : (Real.sqrt 7 + Real.sqrt 10) ^ 2 < (Real.sqrt 3 + Real.sqrt 19) ^ 2 := by
    have h6 : (Real.sqrt 7 + Real.sqrt 10) ^ 2 = Real.sqrt 7 ^2 + Real.sqrt 10 ^2 + 2 * (Real.sqrt 7 * Real.sqrt 10) := by ring
    have h7 : (Real.sqrt 3 + Real.sqrt 19) ^ 2 = Real.sqrt 3 ^2 + Real.sqrt 19 ^2 + 2 * (Real.sqrt 3 * Real.sqrt 19) := by ring
    rw [h6, h7]
    have h8 : Real.sqrt 7 ^ 2 = (7 : ℝ) := Real.sq_sqrt (by norm_num)
    have h9 : Real.sqrt 10 ^ 2 = (10 : ℝ) := Real.sq_sqrt (by norm_num)
    have h10 : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    have h11 : Real.sqrt 19 ^ 2 = (19 : ℝ) := Real.sq_sqrt (by norm_num)
    rw [h8, h9, h10, h11]
    have h12 : Real.sqrt 7 * Real.sqrt 10 = Real.sqrt 70 := by
      have h9 : Real.sqrt 70 = Real.sqrt (7 * (10 : ℝ)) := by norm_num
      rw [h9]
      have h10 : Real.sqrt (7 * (10 : ℝ)) = Real.sqrt (7 : ℝ) * Real.sqrt (10 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num)]
      rw [h10]
      all_goals norm_num
    have h13 : Real.sqrt 3 * Real.sqrt 19 = Real.sqrt 57 := by
      have h9 : Real.sqrt 57 = Real.sqrt (3 * (19 : ℝ)) := by norm_num
      rw [h9]
      have h10 : Real.sqrt (3 * (19 : ℝ)) = Real.sqrt (3 : ℝ) * Real.sqrt (19 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num)]
      rw [h10]
      all_goals norm_num
    rw [h12, h13]
    have h14 : Real.sqrt 70 ≥ 0 := Real.sqrt_nonneg 70
    have h15 : Real.sqrt 57 ≥ 0 := Real.sqrt_nonneg 57
    have h16 : Real.sqrt 70 ^2 = (70 : ℝ) := Real.sq_sqrt (by norm_num)
    have h17 : Real.sqrt 57 ^2 = (57 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 70, Real.sqrt_nonneg 57, 
      h16, h17,
      sq_nonneg (Real.sqrt 70 - Real.sqrt 57), 
      Real.sqrt_le_sqrt (show (57 : ℝ) ≤ (70 : ℝ) by norm_num),
      mul_nonneg (Real.sqrt_nonneg 70) (Real.sqrt_nonneg 57)
    ]
  nlinarith [Real.sqrt_nonneg 7, Real.sqrt_nonneg 10, 
    Real.sqrt_nonneg 3, Real.sqrt_nonneg 19, 
    h1, h2, h3, h4
  ]