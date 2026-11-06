import Mathlib

theorem inequalities_304625 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b ^ 2 + b / c ^ 2 + c / a ^ 2 ≥ 1 / a + 1 / b + 1 / c := by
  have h1 : 0 < a * b * c := by
    positivity

  have h2 : a / b ^ 2 + b / c ^ 2 + c / a ^ 2 - (1 / a + 1 / b + 1 / c) ≥ 0 := by
    have pos1 : 0 < a ^ 2 * b ^ 2 * c ^ 2 := by
      positivity

    have h3 : a / b ^ 2 + b / c ^ 2 + c / a ^ 2 - (1 / a + 1 / b + 1 / c) =
      (a ^ 3 * c ^ 2 + a  ^ 2 * b ^ 3 + b ^ 2 * c ^ 3 - (a * b ^ 2 * c ^ 2 + a ^ 2 * b * c ^ 2 + a ^ 2 * b ^ 2 * c)) / (a ^ 2 * b ^ 2 * c ^ 2) := by
      field_simp
      ring
    rw [h3] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
    all_goals positivity

  linarith [h2]