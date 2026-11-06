import Mathlib

theorem inequalities_271274 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
  have positivity : 0 < (b + c) * (c + a) * (a + b) := by 
    positivity

  have h1 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have eq1 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
        (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 3 / 2 * (b + c) * (c + a) * (a + b)) /
          ((b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [eq1]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    positivity
  linarith [h1]