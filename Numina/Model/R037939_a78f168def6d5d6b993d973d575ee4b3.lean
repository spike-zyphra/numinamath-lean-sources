import Mathlib

theorem algebra_19838 : √30 + √50 ∈ Set.Ioo 12 13 := by
  constructor
  · -- Prove 12 < √30 + √50
    have h1 : 12 < Real.sqrt 30 + Real.sqrt 50 := by
      have h2 : (Real.sqrt 30 + Real.sqrt 50) ^2 > (12 : ℝ) ^2 := by
        have h3 : (Real.sqrt 30 + Real.sqrt 50) ^2 = (Real.sqrt 30) ^2 + (Real.sqrt 50) ^2 + 2 * (Real.sqrt 30 * Real.sqrt 50) := by ring
        have h4 : (Real.sqrt 30) ^2 = 30 := Real.sq_sqrt (by norm_num)
        have h5 : (Real.sqrt 50) ^2 = 50 := Real.sq_sqrt (by norm_num)
        have h6 : Real.sqrt 30 * Real.sqrt 50 = Real.sqrt 1500 := by 
          have h7 : Real.sqrt 30 * Real.sqrt 50 = Real.sqrt (30 * 50 : ℝ) := by 
            rw [← Real.sqrt_mul (by norm_num)]
          have h8 : (30 * 50 : ℝ) = 1500 := by norm_num
          rw [h7, h8]
        have h7 : Real.sqrt 1500 > (32 : ℝ) := by 
          have h32 : (32 : ℝ) < Real.sqrt 1500 := by
            rw [Real.lt_sqrt] <;> norm_num
          linarith
        nlinarith [h3, h4, h5, h6, Real.sqrt_nonneg 1500, Real.sqrt_nonneg 30, Real.sqrt_nonneg 50, h7]
      nlinarith [Real.sqrt_nonneg 30, Real.sqrt_nonneg 50, Real.sqrt_nonneg 30, Real.sqrt_nonneg 50, Real.sqrt_nonneg 30, Real.sqrt_nonneg 50]
    linarith
  · -- Prove √30 + √50 < 13
    have h3 : Real.sqrt 30 + Real.sqrt 50 < (13 : ℝ) := by
      have h3' : (Real.sqrt 30 + Real.sqrt 50) ^2 < (13 : ℝ) ^2 := by
        have h3 : (Real.sqrt 30 + Real.sqrt 50) ^2 = (Real.sqrt 30) ^2 + (Real.sqrt 50) ^2 + 2 * (Real.sqrt 30 * Real.sqrt 50) := by ring
        have h4 : (Real.sqrt 30) ^2 = 30 := Real.sq_sqrt (by norm_num)
        have h5 : (Real.sqrt 50) ^2 = 50 := Real.sq_sqrt (by norm_num)
        have h6 : Real.sqrt 30 * Real.sqrt 50 = Real.sqrt 1500 := by 
          have h7 : Real.sqrt 30 * Real.sqrt 50 = Real.sqrt (30 * 50 : ℝ) := by 
            rw [← Real.sqrt_mul (by norm_num)]
          have h8 : (30 * 50 : ℝ) = 1500 := by norm_num
          rw [h7, h8]
        have h7 : Real.sqrt 1500 < (44.5 : ℝ) := by 
          have h345 : Real.sqrt 1500 < (44.5 : ℝ) := by
            rw [Real.sqrt_lt] <;> norm_num
          linarith
        nlinarith [h3, h4, h5, h6, Real.sqrt_nonneg 1500, Real.sqrt_nonneg 30, Real.sqrt_nonneg 50, h7]
      nlinarith [Real.sqrt_nonneg 30, Real.sqrt_nonneg 50, Real.sqrt_nonneg 30, Real.sqrt_nonneg 50, Real.sqrt_nonneg 30, Real.sqrt_nonneg 50]
    linarith