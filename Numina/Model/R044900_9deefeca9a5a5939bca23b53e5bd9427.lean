import Mathlib

theorem inequalities_597899 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c ≤ 1) :
    (a + b) / c + (b + c) / a + (c + a) / b ≥ 2 * (a + b + c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : (a + b) / c + (b + c) / a + (c + a) / b - 2 * (a + b + c) ≥ 0 := by
    have h3 : (a + b) / c + (b + c) / a + (c + a) / b - 2 * (a + b + c) =
        ((a + b) * (a * b) + (b + c) * (b * c) + (c + a) * (c * a) - 2 * (a + b + c) * (a * b * c)) / (a * b * c) := by
      field_simp [hc.ne', ha.ne', hb.ne']
      ring
    rw [h3] at *
    apply div_nonneg
    · -- Show that numerator is ≥ 0.
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b)),
          mul_nonneg (show 0 ≤ 1 - a * b * c by linarith [habc]) (show 0 ≤ a * b * c by positivity),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
          ]
    · -- Show that denominator is ≥ 0.
      positivity
  linarith