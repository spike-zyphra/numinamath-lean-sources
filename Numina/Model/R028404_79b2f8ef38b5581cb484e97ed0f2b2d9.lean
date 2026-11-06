import Mathlib

theorem inequalities_137592
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    a * b / (a + b) + b * c / (b + c) + c * a / (c + a) ≤
    3 * (a * b + b * c + c * a) / (2 * (a + b + c)) := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  have h2 : 0 < a + b := by
    nlinarith

  have h3 : 0 < b + c := by
    nlinarith

  have h4 : 0 < c + a := by
    nlinarith

  have h5 : 0 < a + b + c := by
    linarith

  have h6 : a * b / (a + b) + b * c / (b + c) + c * a / (c + a) - 3 * (a * b + b * c + c * a) / (2 * (a + b + c)) ≤ 0 := by

    have h7 : 0 < 2 * (a + b + c) * (a + b) * (b + c) * (c + a) := by
      positivity

    have h8 : a * b / (a + b) + b * c / (b + c) + c * a / (c + a) - 3 * (a * b + b * c + c * a) / (2 * (a + b + c)) ≤ 0 := by
      have h9 : a * b / (a + b) + b * c / (b + c) + c * a / (c + a) - 3 * (a * b + b * c + c * a) / (2 * (a + b + c)) = (2 * (a + b + c) * a * b * (b + c) * (c + a) + 2 * (a + b + c) * b * c * (a + b) * (c + a) + 2 * (a + b + c) * c * a * (a + b) * (b + c) - 3 * (a * b + b * c + c * a) * (a + b) * (b + c) * (c + a)) / (2 * (a + b + c) * (a + b) * (b + c) * (c + a)) := by
        field_simp
        ring
      rw [h9] at *
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show that the numerator is non-positive
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
          sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
          sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc 
        ]
      · -- Show that the denominator is non-negative
        positivity

    linarith

  linarith