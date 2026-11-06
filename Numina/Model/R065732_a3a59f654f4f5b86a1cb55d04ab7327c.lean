import Mathlib

theorem inequalities_100267 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2^x * x + 2^y * y ≥ 2^y * x + 2^x * y := by 
  have h : (2:ℝ) ^ x * x + (2:ℝ) ^ y * y - (2:ℝ) ^ y * x - (2:ℝ) ^ x * y ≥ 0 := by
    have h1 : (2:ℝ) ^ x * x + (2:ℝ) ^ y * y - (2:ℝ) ^ y * x - (2:ℝ) ^ x * y = 
          ((2 : ℝ) ^ x - (2 : ℝ) ^ y) * (x - y) := by 
      ring 
    rw [h1]
    by_cases h4 : x ≥ y 
    · -- If x ≥ y 
      have h5 : (2 : ℝ) ^ x ≥ (2 : ℝ) ^ y := by 
        apply Real.rpow_le_rpow_of_exponent_le 
        all_goals linarith 
      have h6 : (2 : ℝ) ^ x - (2 : ℝ) ^ y ≥ 0 := by linarith 
      have h7 : x - y ≥ 0 := by linarith 
      nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) x, Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) y]
    · -- F not (x ≥ y), so y > x 
      have h5 : y > x := by linarith 
      have h6 : (2 : ℝ) ^ y > (2 : ℝ) ^ x := by 
        apply Real.rpow_lt_rpow_of_exponent_lt 
        all_goals linarith 
      have h7 : (2 : ℝ) ^ x - (2 : ℝ) ^ y < 0 := by linarith 
      have h8 : x - y < 0 := by linarith 
      nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) x, Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) y]
  linarith [h]
  all_goals nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) x, Real.rpow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) y]