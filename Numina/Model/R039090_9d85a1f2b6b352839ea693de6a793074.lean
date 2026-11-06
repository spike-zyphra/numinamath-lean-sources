import Mathlib

open Real

theorem algebra_160164 {x : ℝ} (hx : x = 3) :
    sqrt (x - 2 * sqrt 2) / sqrt (x^2 - 4 * x * sqrt 2 + 8) -
    sqrt (x + 2 * sqrt 2) / sqrt (x^2 + 4 * x * sqrt 2 + 8) = 2 := by 
  rw [hx]
  have h1 : sqrt (3 - 2 * sqrt 2) = Real.sqrt 2 - 1 := by
    have h2 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h3 : (3 - 2 * Real.sqrt 2 : ℝ) = (Real.sqrt 2 - 1) ^ 2 := by
      nlinarith [h2, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
    have h4 : sqrt (3 - 2 * Real.sqrt 2) = sqrt ((Real.sqrt 2 - 1) ^ 2) := by 
      rw [h3]
    have h5 : sqrt ((Real.sqrt 2 - 1) ^ 2) = Real.sqrt 2 - 1 := by 
      rw [Real.sqrt_sq]
      have h6 : Real.sqrt 2 > 1 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      linarith 
    rw [h4, h5]
  -- Simplify sqrt(3 + 2 * sqrt 2)
  have h2 : sqrt (3 + 2 * sqrt 2) = Real.sqrt 2 + 1 := by 
    have h3 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h4 : (3 + 2 * Real.sqrt 2 : ℝ) = (Real.sqrt 2 + 1) ^ 2 := by
      nlinarith [h3, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    have h5 : sqrt (3 + 2 * Real.sqrt 2) = sqrt ((Real.sqrt 2 + 1) ^ 2) := by 
      rw [h4]
    have h6 : sqrt ((Real.sqrt 2 + 1) ^ 2) = Real.sqrt 2 + 1 := by 
      rw [Real.sqrt_sq]
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h5, h6]
  have h3 : sqrt ((3 : ℝ) ^ 2 - 4 * (3 : ℝ) * sqrt 2 + 8) = (3 - 2 * sqrt 2 : ℝ) := by 
    have h4 : (3 : ℝ) ^ 2 - 4 * (3 : ℝ) * sqrt 2 + 8 = (3 - 2 * sqrt 2) ^ 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h5 : sqrt ((3 : ℝ) ^ 2 - 4 * (3 : ℝ) * sqrt 2 + 8) = sqrt ((3 - 2 * sqrt 2) ^ 2) := by 
      rw [h4]
    have h6 : sqrt ((3 - 2 * sqrt 2) ^ 2) = (3 - 2 * sqrt 2 : ℝ) := by 
      rw [Real.sqrt_sq]
      have h7 : Real.sqrt 2 < (3 / 2 : ℝ) := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h5, h6]

  have h4 : sqrt ((3 : ℝ) ^ 2 + 4 * (3 : ℝ) * sqrt 2 + 8) = (3 + 2 * sqrt 2 : ℝ) := by 
    have h5 : (3 : ℝ) ^ 2 + 4 * (3 : ℝ) * sqrt 2 + 8 = (3 + 2 * sqrt 2) ^ 2 := by 
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h6 : sqrt ((3 : ℝ) ^ 2 + 4 * (3 : ℝ) * sqrt 2 + 8) = sqrt ((3 + 2 * sqrt 2 : ℝ) ^ 2) := by 
      rw [h5]
    have h7 : sqrt ((3 + 2 * sqrt 2 : ℝ) ^ 2) = (3 + 2 * sqrt 2 : ℝ) := by 
      rw [Real.sqrt_sq]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h6, h7]

  rw [h1, h3, h2, h4]
  have h5 : ((3 - 2 * Real.sqrt 2) : ℝ) ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  -- Prove the denominator of the second fraction is non-zero
  have h6 : ((3 + 2 * Real.sqrt 2) : ℝ) ≠ 0 := by 
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  field_simp [h5, h6]
  <;> ring_nf <;> norm_num
  <;> ring_nf
  all_goals linarith