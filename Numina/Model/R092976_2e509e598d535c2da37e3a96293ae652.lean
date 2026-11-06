import Mathlib

theorem inequalities_601277 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    3 / 4 ≤ a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) +
    c / ((c + 1) * (a + 1)) := by
  have h₁ : a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) - 3 / 4 ≥ 0 := by
    have h₁a : 0 < (a + 1) * (b + 1) * (c + 1) := by
      positivity
    have h₂ : a / ((a + 1) * (b + 1)) + b / ((b + 1) * (c + 1)) + c / ((c + 1) * (a + 1)) - 3 / 4 =
      (a * (c + 1) + b * (a + 1) + c * (b + 1) - 3 / 4 * ((a + 1) * (b + 1) * (c + 1)) ) / ((a + 1) * (b + 1) * (c + 1)) := by
      field_simp
      ring
    rw [h₂]
    apply div_nonneg
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc
      ]
    positivity
  linarith