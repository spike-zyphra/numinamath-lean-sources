import Mathlib

theorem inequalities_35994 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 + 2 * b ^ 2) / (b + c) + (b ^ 2 + 2 * c ^ 2) / (c + a) +
    (c ^ 2 + 2 * a ^ 2) / (a + b) ≥
    3 / 2 * (a + b + c) := by
  have h₁ : 0 < b + c := by linarith
  have h₂ : 0 < c + a := by linarith
  have h₃ : 0 < a + b := by linarith
  have h₄ : (a ^ 2 + 2 * b ^ 2) / (b + c) + (b ^ 2 + 2 * c ^ 2) / (c + a) + (c ^ 2 + 2 * a ^ 2) / (a + b) - 3 / 2 * (a + b + c) ≥ 0 := by
    have h₅ : (a ^ 2 + 2 * b ^ 2) / (b + c) + (b ^ 2 + 2 * c ^ 2) / (c + a) + (c ^ 2 + 2 * a ^ 2) / (a + b) - 3 / 2 * (a + b + c) =
        ((a ^ 2 + 2 * b ^ 2) * (c + a) * (a + b) + (b ^ 2 + 2 * c ^ 2) * (b + c) * (a + b) + (c ^ 2 + 2 * a ^ 2) * (b + c) * (c + a) - 3 / 2 * (a + b + c) * ((b + c) * (c + a) * (a + b))) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      ring
    rw [h₅]
    have h₆ : (b + c) * (c + a) * (a + b) > 0 := by positivity
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
    all_goals positivity
  linarith