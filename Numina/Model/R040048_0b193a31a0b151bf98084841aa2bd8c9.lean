import Mathlib

theorem inequalities_41711 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a^2 + b^2 + c^2 + a + b + c = 6) :
    2 * (1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2) ≥ 3 + 1 / a + 1 / b + 1 / c := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals nlinarith
  have h11 : 2 * (1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2) - (3 + 1 / a + 1 / b + 1 / c) ≥ 0 := by
    have h4 : 2 * (1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2) - (3 + 1 / a + 1 / b + 1 / c) =
        (2 * (b^2 * c^2 + a^2 * c^2 + a^2 * b^2) - (3 * a^2 * b^2 * c^2 + b^2 * c^2 * a + a^2 * c^2 * b + a^2 * b^2 * c)) / (a^2 * b^2 * c^2) := by
      field_simp
      ring
    rw [h4] at *
    have h11 : 2 * (b^2 * c^2 + a^2 * c^2 + a^2 * b^2) - (3 * a^2 * b^2 * c^2 + b^2 * c^2 * a + a^2 * c^2 * b + a^2 * b^2 * c) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * b + b * c + c * a - 3), sq_nonneg (a * b * c - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
      mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
      mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith), 
      mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ a by linarith)]
    apply div_nonneg
    linarith
    positivity

  linarith