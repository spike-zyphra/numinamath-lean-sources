import Mathlib

theorem inequalities_236749 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * a / (a^2 + b * c) + 2 * b / (b^2 + c * a) + 2 * c / (c^2 + a * b) ≤
    a / (b * c) + b / (c * a) + c / (a * b) := by

  have h1 : 0 < a * b * c := by
    positivity

  have h2 : 2 * a / (a^2 + b * c) + 2 * b / (b^2 + c * a) + 2 * c / (c^2 + a * b) - (a / (b * c) + b / (c * a) + c / (a * b)) ≤ 0 := by

    have h3 : 2 * a / (a^2 + b * c) + 2 * b / (b^2 + c * a) + 2 * c / (c^2 + a * b) - (a / (b * c) + b / (c * a) + c / (a * b)) =
        ( (2 * a^2 * b * c / (a^2 + b * c) + 2 * a * b^2 * c / (b^2 + c * a) + 2 * a * b * c^2 / (c^2 + a * b) - (a^2 + b^2 + c^2)) ) / (a * b * c) := by
      field_simp
      ring

    rw [h3] at *
    have h4 : (2 * a^2 * b * c / (a^2 + b * c) + 2 * a * b^2 * c / (b^2 + c * a) + 2 * a * b * c^2 / (c^2 + a * b) - (a^2 + b^2 + c^2)) ≤ 0 := by

      have h6 : 2 * a^2 * b * c / (a^2 + b * c) ≤ (a^2 + b * c) / 2 := by
        have h7 : 0 < a^2 + b * c := by positivity
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [sq_nonneg (a^2 - b * c), sq_nonneg (a * b - a * c), sq_nonneg (b * c - a^2), sq_nonneg (a^2 + b * c - 2 * a * b), sq_nonneg (a^2 + b * c - 2 * a * c), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]

      have h7 : 2 * a * b^2 * c / (b^2 + c * a) ≤ (b^2 + c * a) / 2 := by
        have h8 : 0 < b^2 + c * a := by positivity
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [sq_nonneg (b^2 - c * a), sq_nonneg (b * c - b * a), sq_nonneg (c * a - b^2), sq_nonneg (b^2 + c * a - 2 * b * c), sq_nonneg (b^2 + c * a - 2 * b * a), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]

      have h8 : 2 * a * b * c^2 / (c^2 + a * b) ≤ (c^2 + a * b) / 2 := by
        have h9 : 0 < c^2 + a * b := by positivity
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [sq_nonneg (c^2 - a * b), sq_nonneg (c * a - c * b), sq_nonneg (a * b - c^2), sq_nonneg (c^2 + a * b - 2 * c * a), sq_nonneg (c^2 + a * b - 2 * c * b), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]

      have h9 : 2 * a^2 * b * c / (a^2 + b * c) + 2 * a * b^2 * c / (b^2 + c * a) + 2 * a * b * c^2 / (c^2 + a * b) ≤ (a^2 + b * c) / 2 + (b^2 + c * a) / 2 + (c^2 + a * b) / 2 := by
        linarith [h6, h7, h8]

      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]

    have h3 : ( (2 * a^2 * b * c / (a^2 + b * c) + 2 * a * b^2 * c / (b^2 + c * a) + 2 * a * b * c^2 / (c^2 + a * b) - (a^2 + b^2 + c^2)) ) / (a * b * c) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg h4 (by positivity)

    linarith

  linarith