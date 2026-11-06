import Mathlib

theorem inequalities_603664 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 / (b * c) + b ^ 3 / (a * c) + c ^ 3 / (a * b) ≥ a + b + c := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h4 : a ^ 4 + b ^ 4 + c ^ 4 - a * b * c * (a + b + c) ≥ 0 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h5 : a ^ 3 / (b * c) + b ^ 3 / (a * c) + c ^ 3 / (a * b) - (a + b + c) ≥ 0 := by
    have h6 : a * b * c > 0 := h1
    have h7 : (a ^ 3 / (b * c) + b ^ 3 / (a * c) + c ^ 3 / (a * b) - (a + b + c)) =
        ((a ^ 4 + b ^ 4 + c ^ 4 - a * b * c * (a + b + c)) ) / (a * b * c) := by
      field_simp [show b ≠ 0 by linarith, show a ≠ 0 by linarith, show c ≠ 0 by linarith]
      ring_nf
      <;> 
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    rw [h7]
    -- Since the numerator ≥ 0 by h4 and the denominator > 0 by h6, division is ≥ 0
    apply div_nonneg
    linarith 
    all_goals nlinarith [show 0 < a * b * c from by positivity]
  linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith
  all_goals nlinarith
  all_goals linarith