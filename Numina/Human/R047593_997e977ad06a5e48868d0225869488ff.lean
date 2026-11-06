import Mathlib

theorem inequalities_599246 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    25 < (1 + 4 * a / (b + c)) * (1 + 4 * b / (c + a)) * (1 + 4 * c / (a + b)) := by
  -- prove some positivity
  have h1 : 0 < b + c := by nlinarith
  have h2 : 0 < c + a := by nlinarith
  have h3 : 0 < a + b := by nlinarith

  have h4 : (1 + 4 * a / (b + c)) * (1 + 4 * b / (c + a)) * (1 + 4 * c / (a + b)) - 25 > 0 := by
    have h_pos1 : 0 < (b + c) * (c + a) * (a + b) := by
      apply mul_pos
      apply mul_pos
      all_goals linarith

    have h_mul : ((1 + 4 * a / (b + c)) * (1 + 4 * b / (c + a)) * (1 + 4 * c / (a + b)) - 25) * ((b + c) * (c + a) * (a + b)) > 0 := by
      have h1 : (1 + 4 * a / (b + c)) * (b + c) = (b + c) + 4 * a := by
        field_simp [show b + c ≠ 0 by linarith]
      have h2 : (1 + 4 * b / (c + a)) * (c + a) = (c + a) + 4 * b := by
        field_simp [show c + a ≠ 0 by linarith]
      have h3 : (1 + 4 * c / (a + b)) * (a + b) = (a + b) + 4 * c := by
        field_simp [show a + b ≠ 0 by linarith]
      have h4 : ((1 + 4 * a / (b + c)) * (1 + 4 * b / (c + a)) * (1 + 4 * c / (a + b)) - 25) * ((b + c) * (c + a) * (a + b)) = 
        ((b + c + 4 * a) * (c + a + 4 * b) * (a + b + 4 * c) - 25 * (b + c) * (c + a) * (a + b)) := by
        field_simp [show b + c ≠ 0 by linarith, show c + a ≠ 0 by linarith, show a + b ≠ 0 by linarith]
        ring
      rw [h4]
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a + b + c),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b)]
    have h5 : ((1 + 4 * a / (b + c)) * (1 + 4 * b / (c + a)) * (1 + 4 * c / (a + b)) - 25) > 0 := by
      apply (mul_pos_iff_of_pos_right h_pos1).mp at h_mul
      linarith
    linarith
  linarith