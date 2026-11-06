import Mathlib

theorem inequalities_603534 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c)^2 + b / (c + a)^2 + c / (a + b)^2 ≥ 9 / (4 * (a + b + c)) := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith
  have h3 : a / (b + c) ^ 2 + b / (c + a) ^ 2 + c / (a + b) ^ 2 - 9 / (4 * (a + b + c)) ≥ 0 := by
    have h4 : a / (b + c) ^ 2 + b / (c + a) ^ 2 + c / (a + b) ^ 2 - 9 / (4 * (a + b + c)) =
          (4 * a * (a + b + c) * (c + a) ^ 2 * (a + b) ^ 2 + 4 * b * (a + b + c) * (b + c) ^ 2 * (a + b) ^ 2 + 4 * c * (a + b + c) * (b + c) ^ 2 * (c + a) ^ 2 - 9 * (b + c) ^ 2 * (c + a) ^ 2 * (a + b) ^ 2) / (4 * (a + b + c) * (b + c) ^ 2 * (c + a) ^ 2 * (a + b) ^ 2) := by
      field_simp
      ring
    have h5 : (4 * (a + b + c) * (b + c) ^ 2 * (c + a) ^ 2 * (a + b) ^ 2) > 0 := by
      positivity
    rw [h4]
    apply div_nonneg
    -- Prove numerator is non-negative
    nlinarith [sq_nonneg (a * (c + a) * (a + b) - b * (b + c) * (a + b)), sq_nonneg (b * (b + c) * (a + b) - c * (b + c) * (c + a)), sq_nonneg (c * (b + c) * (c + a) - a * (c + a) * (a + b)), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a * (c + a) - b * (b + c)), sq_nonneg (b * (a + b) - c * (b + c)), sq_nonneg (a * (a + b) - c * (c + a)), sq_nonneg (a * (a + b + c) - b * (a + b + c)), sq_nonneg (b * (a + b + c) - c * (a + b + c)), sq_nonneg (a * (c + a) - b * (b + c)), sq_nonneg (a * (a + b) - c * (c + a)), sq_nonneg (b * (a + b) - c * (b + c)), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < b + c by linarith) (show 0 < c + a by linarith), mul_pos (show 0 < b + c by linarith) (show 0 < a + b by linarith), mul_pos (show 0 < c + a by linarith) (show 0 < a + b by linarith), mul_pos (show 0 < a by linarith) (show 0 < b by linarith), mul_pos (show 0 < a by linarith) (show 0 < c by linarith), mul_pos (show 0 < b by linarith) (show 0 < c by linarith)]
    -- Prove denominator is non-negative
    positivity
  linarith [h3]