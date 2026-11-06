import Mathlib

theorem inequalities_597914 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith

  have h4 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
    have pos1 : 0 < (b + c) * (c + a) * (a + b) := by positivity
    have eq1 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
      (2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b)) /
      (2 * (b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [eq1]
    apply div_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
    positivity

  linarith