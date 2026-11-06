import Mathlib

theorem algebra_236 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : 1 / a - 1 / b - (1 / (a + b)) = 0) :
    ((b / a) ^ 3 + (a / b) ^ 3) = 2 * Real.sqrt 5 := by
  have h1 : a + b > 0 := by linarith
  have h2 : b ^ 2 - a * b - a ^ 2 = 0 := by
    field_simp [(show a ≠ 0 by linarith), (show b ≠ 0 by linarith), (show a + b ≠ 0 by linarith)] at h
    nlinarith [mul_pos ha hb, mul_pos ha (show 0 < a + b by linarith), mul_pos hb (show 0 < a + b by linarith)]
  have h3 : b ^ 2 = a * b + a ^ 2 := by linarith
  have h4 : (b / a) + (a / b) = Real.sqrt 5 := by
    have h5 : ((b / a) + (a / b)) ^ 2 = 5 := by
      have eq1 : (b / a) + (a / b) = (b ^ 2 + a ^ 2) / (a * b) := by
        field_simp [(show a ≠ 0 by linarith), (show b ≠ 0 by linarith)]
        <;> nlinarith
      rw [eq1]
      have eq2 : (b ^ 2 + a ^ 2) ^ 2 = 5 * (a * b) ^ 2 := by
        have h7 : b ^ 2 = a * b + a ^ 2 := by linarith
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 * b^2), sq_nonneg (a * b)]
      field_simp [(show a ≠ 0 by linarith), (show b ≠ 0 by linarith)]
      nlinarith [Real.sqrt_nonneg 5]
    have h6 : ((b / a) + (a / b)) ≥ 0 := by
      have h7 : 0 < b / a := by positivity
      have h8 : 0 < a / b := by positivity
      linarith
    have h7 : Real.sqrt (((b / a) + (a / b)) ^ 2) = Real.sqrt (5 : ℝ) := by
      rw [h5]
    have h8 : Real.sqrt (((b / a) + (a / b)) ^ 2) = (b / a + a / b) := by
      rw [Real.sqrt_sq (show (0 : ℝ) ≤ (b / a + a / b) by linarith [h6])]
    linarith [h7, h8, Real.sqrt_nonneg 5]
  have h6 : (b / a) * (a / b) = 1 := by 
    field_simp [(show a ≠ 0 by linarith), (show b ≠ 0 by linarith)]
  have h7 : (b / a) ^ 3 + (a / b) ^ 3 = ((b / a) + (a / b)) ^ 3 - 3 * ((b / a) * (a / b)) * ((b / a) + (a / b)) := by 
    ring 
  rw [h7, h4, h6]
  have h8 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by nlinarith)
  have h9 : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by
    calc
      Real.sqrt 5 ^ 3 = Real.sqrt 5 ^ 2 * Real.sqrt 5 := by ring
      _ = 5 * Real.sqrt 5 := by rw [h8]
  nlinarith [h8, h9, Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by nlinarith)]