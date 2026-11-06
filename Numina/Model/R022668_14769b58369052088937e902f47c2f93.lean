import Mathlib

theorem inequalities_598741
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a * b + b * c + c * a + 2 * a * b * c = 1) :
    1 ≤ 1 / (4 * a + 1) + 1 / (4 * b + 1) + 1 / (4 * c + 1) := by

  have h1 : 0 < (4 * a + 1) * (4 * b + 1) * (4 * c + 1) := by
    positivity

  have h2 : 1 / (4 * a + 1) + 1 / (4 * b + 1) + 1 / (4 * c + 1) - 1 ≥ 0 := by

    have h3 : 1 / (4 * a + 1) + 1 / (4 * b + 1) + 1 / (4 * c + 1) - 1 =
        ((4 * b + 1) * (4 * c + 1) + (4 * a + 1) * (4 * c + 1) + (4 * a + 1) * (4 * b + 1) - (4 * a + 1) * (4 * b + 1) * (4 * c + 1)) / ((4 * a + 1) * (4 * b + 1) * (4 * c + 1)) := by
      field_simp
      <;> ring

    rw [h3] at *
    apply div_nonneg
    · -- Show that the numerator is non-negative
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
      ]
    · -- Show that the denominator is positive
      positivity

  linarith [h2]