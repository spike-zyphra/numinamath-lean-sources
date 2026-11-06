import Mathlib

theorem algebra_129651 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (Real.sqrt (a * b / 2) + Real.sqrt 8) / Real.sqrt (((a * b + 16) / 8) + Real.sqrt (a * b)) = 2 := by

  have h1 : 0 < a * b := mul_pos ha hb
  have h2 : Real.sqrt ((a * b + 16) / 8 + Real.sqrt (a * b)) = (Real.sqrt (a * b) + 4) / Real.sqrt 8 := by
    have h3 : Real.sqrt ((a * b + 16) / 8 + Real.sqrt (a * b)) = Real.sqrt ((Real.sqrt (a * b) + 4) ^ 2 / 8) := by
      have h4 : (a * b + 16) / 8 + Real.sqrt (a * b) = ((Real.sqrt (a * b) + 4) ^ 2) / 8 := by
        nlinarith [Real.sqrt_nonneg (a * b), Real.sq_sqrt (show 0 ≤ a * b by positivity)]
      rw [h4]
    have h5 : Real.sqrt ((Real.sqrt (a * b) + 4) ^ 2 / 8) = (Real.sqrt (a * b) + 4) / Real.sqrt 8 := by 
      have h8 : Real.sqrt ((Real.sqrt (a * b) + 4) ^ 2 / (8 : ℝ)) = Real.sqrt ((Real.sqrt (a * b) + 4) ^ 2) / Real.sqrt (8 : ℝ) := by
        field_simp [Real.sqrt_div, Real.sqrt_nonneg]
        all_goals positivity
      have h9 : Real.sqrt ((Real.sqrt (a * b) + 4 : ℝ) ^ 2) = (Real.sqrt (a * b) + 4) := by 
        rw [Real.sqrt_sq (show 0 ≤ Real.sqrt (a * b) + 4 by positivity)]
      rw [h9] at h8 
      linarith
    rw [h3, h5]

  have h3 : Real.sqrt (a * b / 2) * Real.sqrt 8 = 2 * Real.sqrt (a * b) := by
    have h4 : Real.sqrt (a * b / 2) * Real.sqrt 8 = Real.sqrt ( (a * b / 2) * (8 : ℝ) ) := by 
      rw [← Real.sqrt_mul (by positivity)]
    have h5' : (a * b / 2 : ℝ) * (8 : ℝ) = (4 * (a * b) : ℝ) := by
      ring
    have h6' : Real.sqrt (4 * (a * b : ℝ)) = (2 : ℝ) * Real.sqrt (a * b) := by
      have h7 : Real.sqrt (4 * (a * b : ℝ)) = Real.sqrt (4 : ℝ) * Real.sqrt (a * b : ℝ) := by
        rw [Real.sqrt_mul (by positivity)]
      have h8 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
        rw [Real.sqrt_eq_cases]
        all_goals norm_num 
      rw [h7, h8]
    rw [h4, h5', h6']
    all_goals nlinarith

  have h4 : (Real.sqrt (a * b / 2) + Real.sqrt 8) * Real.sqrt 8 = 2 * Real.sqrt (a * b) + 8 := by 
    calc
      (Real.sqrt (a * b / 2) + Real.sqrt 8) * Real.sqrt 8 
        = Real.sqrt (a * b / 2) * Real.sqrt 8 + (Real.sqrt 8 * Real.sqrt 8) := by ring
      _ = 2 * Real.sqrt (a * b) + (Real.sqrt 8 * Real.sqrt 8) := by 
        rw [h3]
      _ = 2 * Real.sqrt (a * b) + 8 := by 
        have h8 : Real.sqrt 8 * Real.sqrt 8 = 8 := by
          calc
            Real.sqrt 8 * Real.sqrt 8 = (Real.sqrt 8) ^ 2 := by ring
            _ = 8 := by 
              rw [Real.sq_sqrt]
              all_goals norm_num 
        rw [h8]

  have h7 : (Real.sqrt (a * b / 2) + Real.sqrt 8) * Real.sqrt 8 = 2 * (Real.sqrt (a * b) + 4) := by 
    have h8 : (Real.sqrt (a * b / 2) + Real.sqrt 8) * Real.sqrt 8 = 2 * Real.sqrt (a * b) + 8 := h4
    have h9 : 2 * Real.sqrt (a * b) + 8 = 2 * (Real.sqrt (a * b) + 4) := by 
      ring
    linarith [h8, h9]

  rw [h2]
  have h10 : Real.sqrt (a * b) + 4 ≠ 0 := by
    have h71 : Real.sqrt (a * b) ≥ 0 := Real.sqrt_nonneg (a * b)
    nlinarith [ Real.sq_sqrt (show 0 ≤ a * b by positivity) ]
  have eq : (Real.sqrt (a * b / 2) + Real.sqrt 8) / ((Real.sqrt (a * b) + 4) / Real.sqrt 8) = (Real.sqrt (a * b / 2) + Real.sqrt 8) * Real.sqrt 8 / (Real.sqrt (a * b) + 4) := by 
    field_simp
  rw [eq]
  rw [show (Real.sqrt (a * b / 2) + Real.sqrt 8) * Real.sqrt 8 = 2 * (Real.sqrt (a * b) + 4) by linarith [h7] ]
  have h8 : Real.sqrt (a * b) + 4 > 0 := by
    have h71 : Real.sqrt (a * b) ≥ 0 := Real.sqrt_nonneg (a * b)
    nlinarith [ Real.sq_sqrt (show 0 ≤ a * b by positivity) ]
  have h9 : Real.sqrt (a * b) + 4 ≠ 0 := by nlinarith
  field_simp [h9]