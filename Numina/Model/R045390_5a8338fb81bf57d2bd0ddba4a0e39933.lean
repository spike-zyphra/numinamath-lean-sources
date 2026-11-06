import Mathlib

theorem inequalities_77213 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c = 1) :
    3 / 2 ≤ 1 / (a * (a + 1)) + 1 / (b * (b + 1)) + 1 / (c * (c + 1)) := by

  have h3 : 1 / (a * (a + 1)) + 1 / (b * (b + 1)) + 1 / (c * (c + 1)) - 3 / 2 ≥ 0 := by

    have h4 : 0 < a * b * c := by positivity
    have positive1 : 0 < a * b * c * (a + 1) * (b + 1) * (c + 1) := by positivity

    have h5 : 1 / (a * (a + 1)) + 1 / (b * (b + 1)) + 1 / (c * (c + 1)) - 3 / 2 =
        ( b * c * (b + 1) * (c + 1) +
            a * c * (a + 1) * (c + 1) +
            a * b * (a + 1) * (b + 1) - 3 / 2 * a * b * c * (a + 1) * (b + 1) * (c + 1)
        ) / ( a * b * c * (a + 1) * (b + 1) * (c + 1) ) := by
      field_simp
      ring
    rw [h5]

    have positive2 : 0 < a * b * c * (a + 1) * (b + 1) * (c + 1) := by positivity
    have h6 : b * c * (b + 1) * (c + 1) + a * c * (a + 1) * (c + 1) + a * b * (a + 1) * (b + 1) - 3 / 2 * a * b * c * (a + 1) * (b + 1) * (c + 1) ≥ 0 := by
      nlinarith [ sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          sq_nonneg (a * b * c - 1),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a * b from mul_pos ha hb) hc
        ]
    apply div_nonneg
    linarith
    all_goals linarith
  linarith