import Mathlib

theorem inequalities_67191 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a - b) * (a - c) / (2 * a ^ 2 + (b + c) ^ 2) +
    (b - c) * (b - a) / (2 * b ^ 2 + (c + a) ^ 2) +
    (c - a) * (c - b) / (2 * c ^ 2 + (a + b) ^ 2) ≥ 0 := by
  have pos1 : 0 < (2 * a ^ 2 + (b + c) ^ 2 : ℝ) := by
    positivity
  have pos2 : 0 < (2 * b ^ 2 + (c + a) ^ 2 : ℝ) := by
    positivity
  have pos3 : 0 < (2 * c ^ 2 + (a + b) ^ 2 : ℝ) := by
    positivity
  have h5 : (a - b) * (a - c) / (2 * a ^ 2 + (b + c) ^ 2) + (b - c) * (b - a) / (2 * b ^ 2 + (c + a) ^ 2) + (c - a) * (c - b) / (2 * c ^ 2 + (a + b) ^ 2) =
      ( (a - b) * (a - c) * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2) + (b - c) * (b - a) * (2 * a ^ 2 + (b + c) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2) + (c - a) * (c - b) * (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) ) / ( (2 * a ^ 2 + (b + c) ^ 2) * (2 * b ^ 2 + (c + a) ^ 2) * (2 * c ^ 2 + (a + b) ^ 2) ) := by
    field_simp [show 0 < (2 * a ^ 2 + (b + c) ^ 2 : ℝ) by positivity, show 0 < (2 * b ^ 2 + (c + a) ^ 2 : ℝ) by positivity, show 0 < (2 * c ^ 2 + (a + b) ^ 2 : ℝ) by positivity]
    <;> ring
  rw [h5]
  apply div_nonneg
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
    sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
    sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
    sq_nonneg (b * (a - b)), sq_nonneg (b * (a - c)), sq_nonneg (b * (b - c)), 
    sq_nonneg (c * (a - b)), sq_nonneg (c * (a - c)), sq_nonneg (c * (b - c)), 
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
    mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
    mul_pos (show 0 < a  by linarith) (show 0 < c by linarith), 
    mul_pos (show 0 < b by linarith) (show 0 < c by linarith), 
    sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
    mul_pos (mul_pos ha hb) ha, mul_pos (mul_pos ha hb) hb, mul_pos (mul_pos ha hb) hc, 
    mul_pos (mul_pos ha hc) hb, mul_pos (mul_pos ha hc) ha, mul_pos (mul_pos hb hc) ha
  ]
  all_goals positivity