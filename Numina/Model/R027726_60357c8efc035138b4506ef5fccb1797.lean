import Mathlib

theorem algebra_316246 {x : ℝ} (hx : x = 3) :
    Real.sqrt (x - 2 * Real.sqrt 2) / Real.sqrt (x^2 - 4 * Real.sqrt 2 * x + 8) -
    Real.sqrt (x + 2 * Real.sqrt 2) / Real.sqrt (x^2 + 4 * Real.sqrt 2 * x + 8) = 2 := by
  rw [hx]
  have h1 : Real.sqrt (3 - 2 * Real.sqrt 2) = Real.sqrt 2 - 1 := by
    have h2 : (3 - 2 * Real.sqrt 2 : ℝ) = (Real.sqrt 2 - 1) ^ 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h2]
    have h3 : Real.sqrt ((Real.sqrt 2 - 1) ^ 2) = Real.sqrt 2 - 1 := by 
      rw [Real.sqrt_sq (show 0 ≤ Real.sqrt 2 - 1 by
        have h4 : 1 < Real.sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
        linarith [h4, Real.sqrt_nonneg 2]
      )]
    exact h3
  have h1' : Real.sqrt (3 + 2 * Real.sqrt 2) = Real.sqrt 2 + 1 := by
    have h2 : (3 + 2 * Real.sqrt 2 : ℝ) = (Real.sqrt 2 + 1) ^ 2 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h2]
    have h3 : Real.sqrt ((Real.sqrt 2 + 1) ^ 2) = Real.sqrt 2 + 1 := by 
      rw [Real.sqrt_sq (show 0 ≤ Real.sqrt 2 + 1 by
        have h4 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
        linarith [h4]
      )]
    exact h3
  have h3 : Real.sqrt ((3: ℝ) ^ 2 - 4 * Real.sqrt 2 * (3: ℝ) + 8) = (3 - 2 * Real.sqrt 2 : ℝ) := by 
    have h4 : (3: ℝ) ^ 2 - 4 * Real.sqrt 2 * (3: ℝ) + 8 = (3 - 2 * Real.sqrt 2) ^ 2 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h4]
    have h5 : Real.sqrt ((3 - 2 * Real.sqrt 2) ^ 2) = (3 - 2 * Real.sqrt 2 : ℝ) := by 
      rw [Real.sqrt_sq (show 0 ≤ (3 - 2 * Real.sqrt 2 : ℝ) by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      )]
    exact h5
  have h3' : Real.sqrt ((3: ℝ) ^ 2 + 4 * Real.sqrt 2 * (3: ℝ) + 8) = (3 + 2 * Real.sqrt 2 : ℝ) := by 
    have h4 : (3: ℝ) ^ 2 + 4 * Real.sqrt 2 * (3: ℝ) + 8 = (3 + 2 * Real.sqrt 2) ^ 2 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h4]
    have h5 : Real.sqrt ((3 + 2 * Real.sqrt 2) ^ 2) = (3 + 2 * Real.sqrt 2 : ℝ) := by 
      rw [Real.sqrt_sq (show 0 ≤ (3 + 2 * Real.sqrt 2 : ℝ) by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      )]
    exact h5
  rw [h3, h3']
  rw [h1, h1']
  have h6 : (Real.sqrt 2 - 1 : ℝ) / (3 - 2 * Real.sqrt 2 : ℝ) = Real.sqrt 2 + 1 := by
    have h7 : (3 - 2 * Real.sqrt 2) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    field_simp [h7, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h7 : (Real.sqrt 2 + 1 : ℝ) / (3 + 2 * Real.sqrt 2 : ℝ) = Real.sqrt 2 - 1 := by
    have h8 : (3 + 2 * Real.sqrt 2) ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    field_simp [h8, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  rw [h6, h7]
  <;> nlinarith