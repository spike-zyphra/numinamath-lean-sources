import Mathlib

theorem inequalities_105146 {a b : ℝ} (ha : a < 0) (hb : b < 0) (h : a < b) :
    (a^2 + b^2) / (a^2 - b^2) < (a + b) / (a - b) := by
  have h1 : a ^ 2 - b ^ 2 > 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_pos (show (0 : ℝ) - a > 0 by linarith) (show (0 : ℝ) - b > 0 by linarith), sq_pos_of_neg ha, sq_pos_of_neg hb]
  have h2 : a - b < 0 := by linarith
  have h3 : (a^2 + b^2) / (a^2 - b^2) - (a + b) / (a - b) < 0 := by
    have h4 : ((a ^ 2 + b ^ 2) * (a - b) - (a + b) * (a ^ 2 - b^2)) > 0 := by
      nlinarith [mul_pos (show (0 : ℝ) - a > 0 by linarith) (show (0 : ℝ) - b > 0 by linarith),
              mul_pos (show b - a > 0 by linarith) (show (0 : ℝ) - a > 0 by linarith),
              sq_pos_of_neg ha, sq_pos_of_neg hb, mul_pos_of_neg_of_neg (show a < 0 by linarith) (show b < 0 by linarith)]
    have h5 : (a^2 + b^2) / (a^2 - b^2) - (a + b) / (a - b) =
        ((a ^ 2 + b ^ 2) * (a - b) - (a + b) * (a^2 - b^2)) / ((a^2 - b^2) * (a - b)) := by
      field_simp [(show a^2 - b^2 ≠ 0 by nlinarith), (show a - b ≠ 0 by linarith)]
      <;> ring
    rw [h5]
    apply div_neg_of_pos_of_neg
    linarith
    nlinarith
  linarith