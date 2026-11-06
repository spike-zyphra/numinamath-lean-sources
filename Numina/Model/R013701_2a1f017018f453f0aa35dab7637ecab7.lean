import Mathlib

theorem inequalities_1572 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 / (4 * a) + 1 / (4 * b) + 1 / (4 * c) ≥
    1 / (2 * a + b + c) + 1 / (2 * b + c + a) + 1 / (2 * c + a + b) := by

  have h1 : 0 < a * b * c := by
    positivity

  have h2 : 1 / (4 * a) + 1 / (4 * b) + 1 / (4 * c) - (1 / (2 * a + b + c) + 1 / (2 * b + c + a) + 1 / (2 * c + a + b)) ≥ 0 := by

    have pos1 : 0 < (4 * a * b * c * (2 * a + b + c) * (2 * b + c + a) * (2 * c + a + b)) := by
      positivity

    have pos2 : (1 / (4 * a) + 1 / (4 * b) + 1 / (4 * c) - (1 / (2 * a + b + c) + 1 / (2 * b + c + a) + 1 / (2 * c + a + b))) =
      ((b * c * (2 * a + b + c) * (2 * b + c + a) * (2 * c + a + b) ) +
      (a * c * (2 * a + b + c) * (2 * b + c + a) * (2 * c + a + b)) +
      (a * b * (2 * a + b + c) * (2 * b + c + a) * (2 * c + a + b)) -
      (4 * a * b * c * (2 * b + c + a) * (2 * c + a + b)) -
      (4 * a * b * c * (2 * a + b + c) * (2 * c + a + b)) -
      (4 * a * b * c * (2 * a + b + c) * (2 * b + c + a)) ) / (4 * a * b * c * (2 * a + b + c) * (2 * b + c + a) * (2 * c + a + b)) := by
      field_simp
      ring
    rw [pos2] at *
    apply div_nonneg
    ·
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (mul_pos ha hb) hc]
    all_goals positivity

  linarith