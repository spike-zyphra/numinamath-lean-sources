import Mathlib

theorem inequalities_224703 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    1 + 3 / (a * b + b * c + c * a) ≥ 6 / (a + b + c) := by

  have h1 : 0 < a * b + b * c + c * a := by
    positivity

  have h2 : 0 < a + b + c := by
    linarith

  have h3 : 1 + 3 / (a * b + b * c + c * a) - 6 / (a + b + c) ≥ 0 := by

    have h4 : 0 < (a * b + b * c + c * a) * (a + b + c) := by positivity

    have h5 : 1 + 3 / (a * b + b * c + c * a) - 6 / (a + b + c) =
        ((a * b + b * c + c * a) * (a + b + c) + 3 * (a + b + c) - 6 * (a * b + b * c + c * a)) / ((a * b + b * c + c * a) * (a + b + c)) := by
      field_simp
      ring

    rw [h5] at *

    apply div_nonneg

    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a + b + c - 3), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
    ]

    all_goals positivity

  linarith