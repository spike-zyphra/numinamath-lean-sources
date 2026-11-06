import Mathlib

theorem inequalities_239194 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) ≤ 1 := by

  have h1 : a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) - 1 ≤ 0 := by

    have h1 : 0 < a * b * c := by positivity
    have h2 : a * b * c = 1 := habc

    have h3 : a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) - 1 ≤ 0 := by

      have h4 : a / (a ^ 2 + 2) + b / (b ^ 2 + 2) + c / (c ^ 2 + 2) - 1 =
          ( a * (b^2 + 2) * (c^2 + 2) + b * (a^2 + 2) * (c^2 + 2) + c * (a^2 + 2) * (b^2 + 2) - (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ) / ( (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ) := by
        field_simp
        ring
      rw [h4] at *
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Show that the numerator is non-positive.
        have h5 : a * (b^2 + 2) * (c^2 + 2) + b * (a^2 + 2) * (c^2 + 2) + c * (a^2 + 2) * (b^2 + 2) - (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≤ 0 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
              sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
              sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
            ]
        linarith
      · -- Show that the denominator is non-negative.
        positivity
    linarith

  linarith