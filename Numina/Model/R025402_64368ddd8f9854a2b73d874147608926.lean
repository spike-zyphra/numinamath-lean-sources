import Mathlib

theorem algebra_2132 {a b : ℝ} (ha : √7 = a) (hb : √70 = b) : √4.9 = a * b / 10 := by 
  have h2 : √10 = b / a := by
    have h3 : √70 = √7 * √10 := by 
      have h4 : (70 : ℝ) = 7 * 10 := by norm_num 
      have h5 : √70 = √(7 * 10 : ℝ) := by 
        rw [h4] 
      rw [h5]
      rw [Real.sqrt_mul (by norm_num)]
      all_goals norm_num 
    rw [hb, ha] at h3 
    have ha2 : a ≠ 0 := by 
      by_contra h 
      have : √7 = 0 := by linarith [h, ha] 
      have h7 : √7 > 0 := by positivity 
      linarith 
    have h4 : √10 = b / a := by
      field_simp [ha2] at *
      <;> nlinarith 
    exact h4 
  have h1 : √4.9 = 7 / √10 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    <;> ring_nf <;> norm_num
    all_goals linarith 
  rw [h1]
  rw [h2]
  have ha2 : a ^ 2 = 7 := by
    calc 
      a ^ 2 = (√7) ^ 2 := by rw [ha]
      _ = 7 := Real.sq_sqrt (by norm_num)
  -- hb^2 = 70
  have hb2 : b ^ 2 = 70 := by
    calc 
      b ^ 2 = (√70) ^ 2 := by rw [hb]
      _ = 70 := Real.sq_sqrt (by norm_num)
  field_simp [(show b ≠ 0 by 
    by_contra h 
    have : √70 = 0 := by 
      rw [hb]
      linarith 
    have h70 : √70 > 0 := by positivity 
    linarith 
  ), (show a ≠ 0 by 
    by_contra h 
    have : √7 = 0 := by 
      linarith [h, ha] 
    have h7 : √7 > 0 := by positivity 
    linarith 
  )] 
  <;> nlinarith [Real.sqrt_nonneg (7 : ℝ), Real.sqrt_nonneg (10 : ℝ), Real.sqrt_nonneg (70 : ℝ), Real.sqrt_nonneg (4.9 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (70 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (4.9 : ℝ) by norm_num), ha2, hb2]