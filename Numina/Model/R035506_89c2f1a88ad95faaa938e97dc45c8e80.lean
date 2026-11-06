import Mathlib

theorem inequalities_601601
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    9 / 4 ≤ (a ^ 2 + 2 * b * c) / (b + c) ^ 2 +
          (b ^ 2 + 2 * a * c) / (a + c) ^ 2 +
          (c ^ 2 + 2 * a * b) / (a + b) ^ 2 := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < a + c := by linarith
  have h3 : 0 < a + b := by linarith
  have h4 : 0 < (b + c) ^ 2 := by positivity
  have h5 : 0 < (a + c) ^ 2 := by positivity
  have h6 : 0 < (a + b) ^ 2 := by positivity
  have h7 : (a ^ 2 + 2 * b * c) / (b + c) ^ 2 + (b ^ 2 + 2 * a * c) / (a + c) ^ 2 + (c ^ 2 + 2 * a * b) / (a + b) ^ 2 - 9 / 4 ≥ 0 := by
    have h8 : 0 < (b + c) ^ 2 * (a + c) ^ 2 * (a + b) ^ 2 := by positivity
    have h9 : (a ^ 2 + 2 * b * c) / (b + c) ^ 2 + (b ^ 2 + 2 * a * c) / (a + c) ^ 2 + (c ^ 2 + 2 * a * b) / (a + b) ^ 2 - 9 / 4 =
          ((a ^ 2 + 2 * b * c) * (a + c) ^ 2 * (a + b) ^ 2 + (b^2 + 2 * a * c) * (b + c) ^ 2 * (a + b) ^ 2 + (c ^ 2 + 2 * a * b) * (b + c) ^ 2 * (a + c) ^ 2 - 9 / 4 * (b + c) ^ 2 * (a + c) ^ 2 * (a + b) ^ 2) / ((b + c) ^ 2 * (a + c) ^ 2 * (a + b) ^ 2) := by
      field_simp
      ring
    rw [h9]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < b + c by linarith) (show 0 < a + c by linarith), 
          mul_pos (show 0 < b + c by linarith) (show 0 < a + b by linarith), 
          mul_pos (show 0 < a + c by linarith) (show 0 < a + b by linarith)]
    all_goals positivity
  linarith