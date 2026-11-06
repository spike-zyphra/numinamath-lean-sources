import Mathlib

theorem inequalities_292863 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b * c) + b / (a * c) + c / (a * b) ≥ 2 / a + 2 / b - 2 / c := by
  have h1 : a / (b * c) + b / (a * c) + c / (a * b) - (2 / a + 2 / b - 2 / c) ≥ 0 := by
    have h2 : a / (b * c) + b / (a * c) + c / (a * b) - (2 / a + 2 / b - 2 / c) =
      (a^2 + b^2 + c^2 - 2 * b * c - 2 * a * c + 2 * a * b) / (a * b * c) := by
      field_simp
      ring
    rw [h2]
    have h3 : a^2 + b^2 + c^2 - 2 * b * c - 2 * a * c + 2 * a * b ≥ 0 := by
      nlinarith [sq_nonneg (a + b - c)]
    have h4 : a * b * c > 0 := by
      positivity
    apply div_nonneg
    linarith
    positivity
  linarith