import Mathlib

open Real Set

theorem algebra_198515 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 2) :
    (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 ≥ 8 := by
  have h1 : 0 < a * b := by
    nlinarith
  have h2 : a * b ≤ 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), h]
  have h3 : (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 - 8 ≥ 0 := by
    have h4 : (a + 1 / a) ^ 2 + (b + 1 / b) ^ 2 - 8 = a ^ 2 + b ^ 2 + (1 / a ^ 2 + 1 / b ^ 2) - 4 := by 
      field_simp [show a ≠ 0 by linarith, show b ≠ 0 by linarith]
      <;> nlinarith [h, sq_nonneg (a - 1), sq_nonneg (b - 1)]
    rw [h4]
    have h5 : a ^ 2 + b ^ 2 + (1 / a ^ 2 + 1 / b ^ 2) - 4 = (a^4 * b^2 + a^2 * b^4 + a^2 + b^2 - 4 * a^2 * b^2) / (a^2 * b^2) := by 
      field_simp [show a ≠ 0 by linarith, show b ≠ 0 by linarith]
      <;> ring
    rw [h5]
    apply div_nonneg
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a * b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1), 
              sq_nonneg (a^2 * b - a), sq_nonneg (a * b^2 - b), 
              mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
              mul_pos (show 0 < a by linarith) (show 0 < a * b by nlinarith), 
              mul_pos (show 0 < b by linarith) (show 0 < a * b by nlinarith)]
    all_goals nlinarith [mul_pos (show 0 < a by linarith) (show 0 < b by linarith)]
  linarith