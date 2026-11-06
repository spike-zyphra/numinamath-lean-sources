import Mathlib

theorem algebra_320677 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b = Real.sqrt (a * b + 9)) (h2 : b + c = Real.sqrt (b * c + 16))
    (h3 : c + a = Real.sqrt (c * a + 25)) :
    a + b + c = Real.sqrt (25 + 12 * Real.sqrt 3) := by

  have h1_sq : (a + b) ^ 2 = a * b + 9 := by
    calc
      (a + b) ^ 2 = (Real.sqrt (a * b + 9)) ^ 2 := by rw [h1]
      _ = a * b + 9 := by
        have h4 : 0 ≤ a * b + 9 := by
          nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        rw [Real.sq_sqrt h4]

  have h2_sq : (b + c) ^ 2 = b * c + 16 := by
    calc
      (b + c) ^ 2 = (Real.sqrt (b * c + 16)) ^ 2 := by rw [h2]
      _ = b * c + 16 := by
        have h5 : 0 ≤ b * c + 16 := by
          nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        rw [Real.sq_sqrt h5]

  have h3_sq : (c + a) ^ 2 = c * a + 25 := by
    calc
      (c + a) ^ 2 = (Real.sqrt (c * a + 25)) ^ 2 := by rw [h3]
      _ = c * a + 25 := by
        have h6 : 0 ≤ c * a + 25 := by
          nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        rw [Real.sq_sqrt h6]

  have pos1 : 0 < a + b + c := by linarith [ha, hb, hc]

  have h8 : (a + b + c) ^ 2 = 25 + 12 * Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), 
          h1_sq, h2_sq, h3_sq, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h9 : Real.sqrt (25 + 12 * Real.sqrt 3) ≥ 0 := by positivity

  have h8' : (Real.sqrt (25 + 12 * Real.sqrt 3)) ^ 2 = 25 + 12 * Real.sqrt 3 := Real.sq_sqrt (by positivity)

  have h10 : (a + b + c) ^ 2 = (Real.sqrt (25 + 12 * Real.sqrt 3)) ^ 2 := by 
    linarith [h8, h8']

  have h11 : a + b + c = Real.sqrt (25 + 12 * Real.sqrt 3) := by
    nlinarith [Real.sqrt_nonneg (25 + 12 * Real.sqrt 3), pos1, h10]

  exact h11