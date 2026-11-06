import Mathlib

theorem algebra_322405 (x : ℝ) (hx : x = 1 / (Real.sqrt 3 - Real.sqrt 2)) :
    x ^ 6 - 2 * Real.sqrt 2 * x ^ 5 - x ^ 4 + x ^ 3 - 2 * Real.sqrt 3 * x ^ 2 + 2 * x - Real.sqrt 2 = Real.sqrt 3 := by
  have hx' : x = Real.sqrt 3 + Real.sqrt 2 := by
    rw [hx]
    have h1 : Real.sqrt 3 - Real.sqrt 2 ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, 
        Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)]
    field_simp [h1]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, 
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2), 
      sq_pos_of_pos (show 0 < Real.sqrt 3 by positivity), 
      sq_pos_of_pos (show 0 < Real.sqrt 2 by positivity)]
  rw [hx']
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 4 = 9 := by
    calc
      Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
      _ = 3 ^ 2 := by rw [h1]
      _ = 9 := by norm_num
  have h4 : Real.sqrt 2 ^ 4 = 4 := by
    calc
      Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
      _ = 2 ^ 2 := by rw [h2]
      _ = 4 := by norm_num
  have h7 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
    have h12 : (Real.sqrt 3 * Real.sqrt 2) ^ 2 = (6 : ℝ) := by
      calc
        (Real.sqrt 3 * Real.sqrt 2) ^ 2 = (Real.sqrt 3) ^ 2 * (Real.sqrt 2) ^ 2 := by ring
        _ = 3 * 2 := by rw [h1, h2]
        _ = (6 : ℝ) := by norm_num
    have h13 : 0 ≤ Real.sqrt 3 * Real.sqrt 2 := by positivity
    have h14 : Real.sqrt 6 ≥ 0 := Real.sqrt_nonneg 6
    have h15 : (Real.sqrt 3 * Real.sqrt 2) = Real.sqrt 6 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), h12, h13, h14]
    exact h15
  nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, sq_nonneg (Real.sqrt 3 - Real.sqrt 2), sq_nonneg (Real.sqrt 3 + Real.sqrt 2), 
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
    Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
    sq_nonneg ((Real.sqrt 3) ^ 2 - (Real.sqrt 2) ^ 2), 
    mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 2)
  ]