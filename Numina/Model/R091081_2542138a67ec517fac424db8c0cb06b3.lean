import Mathlib

theorem algebra_2424 {x : ℝ} (hx : x = 1 / (Real.sqrt 2 + 1)) :
    (3 / 4) * x ^ 3 + (5 / 2) * x ^ 2 + (5 / 4) * x + 1 = 2 := by 
  have h1 : x = Real.sqrt 2 - 1 := by 
    rw [hx]
    have h2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
    field_simp [(show Real.sqrt 2 + 1 ≠ 0 by nlinarith)]
    <;> ring_nf <;> norm_num
    <;> ring
  rw [h1]
  have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  have h4 : Real.sqrt 2 ^ 3 = Real.sqrt 2 * 2 := by 
    calc 
      Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 := by ring 
      _ = 2 * Real.sqrt 2 := by rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      _ = Real.sqrt 2 * 2 := by ring 
  have h5 : (Real.sqrt 2 - 1 : ℝ) ^ 2 = 3 - 2 * Real.sqrt 2 := by
    calc 
      (Real.sqrt 2 - 1 : ℝ) ^ 2 = (Real.sqrt 2 ^ 2 - 2 * Real.sqrt 2 + 1) := by ring 
      _ = (2 - 2 * Real.sqrt 2 + 1) := by rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      _ = 3 - 2 * Real.sqrt 2 := by ring 
  have h6 : (Real.sqrt 2 - 1 : ℝ) ^ 3 = 5 * Real.sqrt 2 - 7 := by 
    calc 
      (Real.sqrt 2 - 1 : ℝ) ^ 3 = (Real.sqrt 2 - 1) * (Real.sqrt 2 - 1) ^ 2 := by ring 
      _ = (Real.sqrt 2 - 1) * (3 - 2 * Real.sqrt 2) := by rw [h5]
      _ = 3 * Real.sqrt 2 - 2 * (Real.sqrt 2 ^ 2) - 3 + 2 * Real.sqrt 2 := by ring 
      _ = 3 * Real.sqrt 2 - 2 * 2 - 3 + 2 * Real.sqrt 2 := by rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      _ = 5 * Real.sqrt 2 - 7 := by ring 
  have h7 : (Real.sqrt 2 - 1 : ℝ) ^ 3 = 5 * Real.sqrt 2 - 7 := h6
  have h8 : (Real.sqrt 2 - 1 : ℝ) ^ 2 = 3 - 2 * Real.sqrt 2 := h5
  simp only [h7, h8]
  nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2 - 1), sq_nonneg (Real.sqrt 2 + 1)]