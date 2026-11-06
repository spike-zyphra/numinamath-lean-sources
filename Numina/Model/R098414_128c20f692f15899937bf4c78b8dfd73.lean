import Mathlib

theorem algebra_1518 {x y z : ℝ} (h₀ : x - y = Real.sqrt 2 + 1) (h₁ : y - z = Real.sqrt 2 - 1) :
    x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x = 7 := by 
  have h2 : x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x =
    1 / 2 * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by 
      ring 
  have h3 : z - x = -2 * Real.sqrt 2 := by 
    have h4 : z - x = -((x - y) + (y - z)) := by ring 
    rw [h4, h₀, h₁] 
    ring 
  have hxy : (x - y) ^ 2 = 3 + 2 * Real.sqrt 2 := by 
    rw [h₀] 
    calc 
      (Real.sqrt 2 + 1) ^ 2 = (Real.sqrt 2) ^ 2 + 2 * Real.sqrt 2 + 1 := by ring 
      _ = 2 + 2 * Real.sqrt 2 + 1 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      _ = 3 + 2 * Real.sqrt 2 := by ring 
  have hyz : (y - z) ^ 2 = 3 - 2 * Real.sqrt 2 := by 
    rw [h₁] 
    calc 
      (Real.sqrt 2 - 1) ^ 2 = (Real.sqrt 2) ^ 2 - 2 * Real.sqrt 2 + 1 := by ring 
      _ = 2 - 2 * Real.sqrt 2 + 1 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      _ = 3 - 2 * Real.sqrt 2 := by ring 
  have hzx : (z - x) ^ 2 = 8 := by 
    rw [h3] 
    calc 
      (-2 * Real.sqrt 2) ^ 2 = 4 * (Real.sqrt 2) ^ 2 := by ring 
      _ = 4 * 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      _ = 8 := by norm_num 
  rw [h2] 
  rw [hxy, hyz, hzx] 
  <;> linarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0)]