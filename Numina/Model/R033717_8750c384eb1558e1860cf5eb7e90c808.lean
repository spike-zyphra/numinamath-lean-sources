import Mathlib

theorem algebra_196884 : 2 * Real.sqrt (3 + Real.sqrt (5 - Real.sqrt (13 + Real.sqrt 48))) = Real.sqrt 6 + Real.sqrt 2 := by
  have h1 : Real.sqrt 48 = 4 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num 
  have h2 : Real.sqrt (13 + Real.sqrt 48) = 2 * Real.sqrt 3 + 1 := by
    rw [h1]
    have h3 : (2 * Real.sqrt 3 + 1: ℝ) ^ 2 = 13 + (4 * Real.sqrt 3) := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h4 : Real.sqrt (13 + (4 * Real.sqrt 3)) = 2 * Real.sqrt 3 + 1 := by
      rw [←h3]
      rw [Real.sqrt_sq]
      all_goals
        positivity 
    simpa using h4
  have h3 : Real.sqrt (5 - Real.sqrt (13 + Real.sqrt 48)) = Real.sqrt 3 - 1 := by 
    rw [h2]
    have h4 : Real.sqrt 3 > 0 := by
      apply Real.sqrt_pos.mpr 
      norm_num 
    have h5 : Real.sqrt 3 ≥ 1 := by 
      nlinarith [Real.sqrt_pos.mpr (show (1 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (1 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
    have h6 : (Real.sqrt 3 - 1 : ℝ) ≥ 0 := by 
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
    have h7 : (Real.sqrt 3 - 1 : ℝ) ^ 2 = 4 - 2 * Real.sqrt 3 := by 
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
    have h8 : Real.sqrt (4 - 2 * Real.sqrt 3) = Real.sqrt 3 - 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
    have h9 : 5 - (2 * Real.sqrt 3 + 1 : ℝ) = 4 - 2 * Real.sqrt 3 := by 
      ring_nf
    rw [h9]
    exact h8 
  have h4 : Real.sqrt (3 + Real.sqrt (5 - Real.sqrt (13 + Real.sqrt 48))) = Real.sqrt (2 + Real.sqrt 3) := by
    rw [h3]
    have h6 : (3 + (Real.sqrt 3 - 1 : ℝ) : ℝ) = 2 + Real.sqrt 3 := by 
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
    rw [h6]
  have h5 : Real.sqrt (2 + Real.sqrt 3) = (Real.sqrt 6 + Real.sqrt 2) / 2 := by 
    have h6 : ((Real.sqrt 6 + Real.sqrt 2) / 2) ^ 2 = 2 + Real.sqrt 3 := by 
      have h14 : Real.sqrt 6 * Real.sqrt 2 = 2 * Real.sqrt 3 := by 
        calc 
          Real.sqrt 6 * Real.sqrt 2 = Real.sqrt (6 * 2) := by rw [Real.sqrt_mul (by norm_num)]
          _ = Real.sqrt (12 : ℝ) := by norm_num
          _ = Real.sqrt (4 * 3 : ℝ) := by norm_num 
          _ = Real.sqrt 4 * Real.sqrt 3 := by rw [Real.sqrt_mul (by norm_num)]
          _ = (2 : ℝ) * Real.sqrt 3 := by 
            have h144 : Real.sqrt 4 = 2 := by 
              rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
            rw [h144]
          _ = 2 * Real.sqrt 3 := by linarith 
      nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, 
          Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), 
          Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), 
          Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), 
          h14 
        ]
    have h7 : 0 ≤ (Real.sqrt 6 + Real.sqrt 2) / 2 := by
      positivity
    rw [←h6]
    field_simp 
  rw [h4, h5]
  all_goals 
    ring_nf