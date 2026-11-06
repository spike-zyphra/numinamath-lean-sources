import Mathlib

theorem algebra_161341 : (Real.sqrt (5 - 2 * Real.sqrt 6) * (5 + 2 * Real.sqrt 6) * (49 - 20 * Real.sqrt 6)) / (Real.sqrt 27 - 3 * Real.sqrt 18 + 3 * Real.sqrt 12 - Real.sqrt 8) = 1 := by
  have h1 : Real.sqrt (5 - 2 * Real.sqrt 6) = Real.sqrt 3 - Real.sqrt 2 := by
    have h7 : (Real.sqrt 3 - Real.sqrt 2) ^ 2 = 5 - 2 * Real.sqrt 6 := by 
      have h8 : (Real.sqrt 3 - Real.sqrt 2) ^ 2 = (Real.sqrt 3) ^ 2 + (Real.sqrt 2) ^ 2 - 2 * (Real.sqrt 3 * Real.sqrt 2) := by ring
      rw [h8]
      have h9 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      have h10 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have h11 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by 
        have h12 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt (3 * 2 : ℝ) := by 
          rw [← Real.sqrt_mul (by norm_num)]
        have h13 : Real.sqrt (3 * 2 : ℝ) = Real.sqrt 6 := by norm_num
        rw [h12, h13]
      rw [h9, h10, h11]
      <;> nlinarith [show Real.sqrt 6 ≥ 0 by positivity, Real.sqrt_nonneg 6]
    have h6 : 0 ≤ (Real.sqrt 3 - Real.sqrt 2 : ℝ) := by 
      have h7 : Real.sqrt 3 ≥ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
      linarith
    rw [←h7]
    all_goals 
      field_simp [Real.sqrt_nonneg, h6]
  have h11 : Real.sqrt 27 = 3 * Real.sqrt 3 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h12 : Real.sqrt 18 = 3 * Real.sqrt 2 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h13 : Real.sqrt 12 = 2 * Real.sqrt 3 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h14 : Real.sqrt 8 = 2 * Real.sqrt 2 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h2 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h15 : Real.sqrt (5 - 2 * Real.sqrt 6) * (5 + 2 * Real.sqrt 6) = Real.sqrt 3 + Real.sqrt 2 := by 
    rw [h1]
    have h16 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := h2
    rw [h16]
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
              mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)
            ]
  have h17 : Real.sqrt (5 - 2 * Real.sqrt 6) * (5 + 2 * Real.sqrt 6) * (49 - 20 * Real.sqrt 6) = 9 * Real.sqrt 3 - 11 * Real.sqrt 2 := by
    have h18 : Real.sqrt (5 - 2 * Real.sqrt 6) * (5 + 2 * Real.sqrt 6) = Real.sqrt 3 + Real.sqrt 2 := h15
    have h19 : (Real.sqrt (5 - 2 * Real.sqrt 6) * (5 + 2 * Real.sqrt 6) * (49 - 20 * Real.sqrt 6)) = (Real.sqrt (5 - 2 * Real.sqrt 6) * (5 + 2 * Real.sqrt 6)) * (49 - 20 * Real.sqrt 6) := by ring
    rw [h19]
    rw [h18]
    have h20 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := h2
    rw [h20]
    nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
              mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2), 
              show (Real.sqrt 3) ^ 2 = 3 by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)], 
              show (Real.sqrt 2) ^ 2 = 2 by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
            ]
  have h18 : Real.sqrt 27 - 3 * Real.sqrt 18 + 3 * Real.sqrt 12 - Real.sqrt 8 = 9 * Real.sqrt 3 - 11 * Real.sqrt 2 := by 
    rw [h11, h12, h13, h14]
    ring_nf
  rw [h17, h18]
  have h19 : (9 * Real.sqrt 3 - 11 * Real.sqrt 2) ≠ 0 := by 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), 
              Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
              mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)
            ]
  field_simp [h19]