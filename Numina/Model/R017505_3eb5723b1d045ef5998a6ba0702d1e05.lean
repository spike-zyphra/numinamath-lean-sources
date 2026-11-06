import Mathlib

theorem inequalities_602856 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) ≥
    3 / 2 * (a^3 + b^3 + c^3) / (a^2 + b^2 + c^2) := by

  have h1 : 0 < b + c := by
    linarith

  have h2 : 0 < c + a := by
    linarith

  have h3 : 0 < a + b := by
    linarith

  have h5 : a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) - 3 / 2 * (a^3 + b^3 + c^3) / (a^2 + b^2 + c^2) ≥ 0 := by
    have h6 : a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b) - 3 / 2 * (a^3 + b^3 + c^3) / (a^2 + b^2 + c^2) =
        (a^2 * (c + a) * (a + b) * (a^2 + b^2 + c^2) +
        b^2 * (b + c) * (a + b) * (a^2 + b^2 + c^2) +
        c^2 * (b + c) * (c + a) * (a^2 + b^2 + c^2) - 3 / 2 * (a^3 + b^3 + c^3) * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b) * (a^2 + b^2 + c^2)) := by
      field_simp
      ring

    rw [h6]

    have h7 : (b + c) * (c + a) * (a + b) * (a^2 + b^2 + c^2) > 0 := by
      positivity

    have h8 : a^2 * (c + a) * (a + b) * (a^2 + b^2 + c^2) + b^2 * (b + c) * (a + b) * (a^2 + b^2 + c^2) + c^2 * (b + c) * (c + a) * (a^2 + b^2 + c^2) - 3 / 2 * (a^3 + b^3 + c^3) * (b + c) * (c + a) * (a + b) ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc 
        ]

    apply div_nonneg
    · linarith
    all_goals linarith

  linarith [h5]