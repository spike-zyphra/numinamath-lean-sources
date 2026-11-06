import Mathlib

theorem inequalities_318341 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / a + 1 / b + 1 / c + 3 / (a + b + c) ≥ 4 := by
  have h1 : 0 < a + b + c := by
    positivity

  have h2 : 1 / a + 1 / b + 1 / c + 3 / (a + b + c) - 4 ≥ 0 := by
    have pos1 : 0 < a * b * c * (a + b + c) := by
      positivity
    have h3 : 1 / a + 1 / b + 1 / c + 3 / (a + b + c) - 4 =
        (b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) + 3 * (a * b * c) - 4 * (a * b * c * (a + b + c)) ) / (a * b * c * (a + b + c)) := by
      field_simp
      ring
    rw [h3]
    have h4 : b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) + 3 * (a * b * c) - 4 * (a * b * c * (a + b + c)) ≥ 0 := by
      have h3 : a * b * c = 1 := habc
      rw [h3]
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        sq_nonneg (a + b + c - 3), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
        mul_nonneg (mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith)) (show 0 ≤ c by linarith)
      ]
    have pos2 : (a * b * c * (a + b + c) ) > 0 := by positivity
    apply div_nonneg
    linarith
    all_goals linarith
  linarith