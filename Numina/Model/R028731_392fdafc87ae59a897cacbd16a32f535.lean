import Mathlib

theorem inequalities_77655 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 3) :
    a / (1 + b) + b / (1 + c) + c / (1 + a) ≥ 1 / (1 + b) + 1 / (1 + c) + 1 / (1 + a) := by

  have ha1 : 0 < 1 + a := by
    nlinarith
  have hb1 : 0 < 1 + b := by
    nlinarith
  have hc1 : 0 < 1 + c := by
    nlinarith

  have h1 : a / (1 + b) + b / (1 + c) + c / (1 + a) - (1 / (1 + b) + 1 / (1 + c) + 1 / (1 + a)) ≥ 0 := by
    have h2 : a / (1 + b) + b / (1 + c) + c / (1 + a) - (1 / (1 + b) + 1 / (1 + c) + 1 / (1 + a)) =
        ((a - 1) * (1 + c) * (1 + a) + (b - 1) * (1 + b) * (1 + a) + (c - 1) * (1 + b) * (1 + c)) / ((1 + b) * (1 + c) * (1 + a)) := by
      field_simp
      ring
    rw [h2] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      h, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc
    ]
    positivity
  linarith
  all_goals positivity