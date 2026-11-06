import Mathlib

theorem inequalities_277006 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    6 ≤ (a * b * (a + b) + a * c * (a + c) + b * c * (b + c)) / (a * b * c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith [ha, hb, hc]
  have h2 : a * b * (a + b) + a * c * (a + c) + b * c * (b + c) ≥ 6 * a * b * c := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
  have h3 : (a * b * (a + b) + a * c * (a + c) + b * c * (b + c)) / (a * b * c) ≥ 6 := by
    apply (le_div_iff₀ h1).mpr
    nlinarith [h2]
  linarith [h3]