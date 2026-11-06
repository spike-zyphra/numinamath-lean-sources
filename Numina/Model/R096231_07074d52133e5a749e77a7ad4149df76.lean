import Mathlib

theorem inequalities_218018 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * Real.sqrt a + 3 * (b) ^ ((1 : ℝ) / 3) ≥ 5 * (a * b) ^ ((1 : ℝ) / 5) := by
  have h1 : Real.sqrt a > 0 := by 
    apply Real.sqrt_pos.2 
    linarith
  have h2 : (b : ℝ) ^ ((1 : ℝ) / 3) > 0 := by 
    positivity
  have h7 : (2 / 5 : ℝ) + (3 / 5 : ℝ) = 1 := by norm_num
  have h6 : (Real.sqrt a) ^ (2 / 5 : ℝ) * (b ^ (1 / 3 : ℝ)) ^ (3 / 5 : ℝ) ≤ (2 / 5 : ℝ) * Real.sqrt a + (3 / 5 : ℝ) * (b : ℝ) ^ (1 / 3 : ℝ) := by
    have h8 : Real.sqrt a > 0 := by 
      apply Real.sqrt_pos.2 
      linarith
    have h9 : (b : ℝ) ^ (1 / 3 : ℝ) > 0 := by 
      positivity
    have h10 : ((2 / 5 : ℝ) * Real.sqrt a + (3 / 5 : ℝ) * (b ^ (1 / 3 : ℝ))) ≥ Real.sqrt a ^ (2 / 5 : ℝ) * (b ^ (1 / 3 : ℝ)) ^ (3 / 5 : ℝ) := by
      apply Real.geom_mean_le_arith_mean2_weighted 
      all_goals nlinarith
    linarith
  have h8 : (b ^ (1 / 3 : ℝ)) ^ (3 / 5 : ℝ) = b ^ (1 / 5 : ℝ) := by 
    have h9 : (b ^ (1 / 3 : ℝ)) ^ (3 / 5 : ℝ) = b ^ ((1 / 3 : ℝ) * (3 / 5 : ℝ)) := by
      rw [← Real.rpow_mul]
      all_goals linarith [hb]
    rw [h9]
    norm_num
  have h10 : (Real.sqrt a) ^ (2 / 5 : ℝ) = a ^ (1 / 5 : ℝ) := by
    have h11 : Real.sqrt a = a ^ (1 / 2 : ℝ) := by 
      rw [Real.sqrt_eq_rpow]
    rw [h11]
    have h12 : (a ^ (1 / 2 : ℝ)) ^ (2 / 5 : ℝ) = a ^ ((1 / 2 : ℝ) * (2 / 5 : ℝ)) := by
      rw [← Real.rpow_mul]
      all_goals linarith [ha]
    rw [h12]
    norm_num
  have h11 : (Real.sqrt a) ^ (2 / 5 : ℝ) * (b ^ (1 / 3 : ℝ)) ^ (3 / 5 : ℝ) = (a * b) ^ (1 / 5 : ℝ) := by 
    rw [h10, h8]
    have h12 : (a * b) ^ (1 / 5 : ℝ) = (a ^ (1 / 5 : ℝ)) * (b ^ (1 / 5 : ℝ)) := by 
      rw [Real.mul_rpow]
      all_goals linarith [show 0 ≤ a by linarith, show 0 ≤ b by linarith]
    rw [h12]
    <;> nlinarith
  nlinarith [h6, h11, mul_pos ha hb]