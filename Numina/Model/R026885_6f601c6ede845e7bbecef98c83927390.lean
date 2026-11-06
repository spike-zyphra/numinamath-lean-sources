import Mathlib

theorem inequalities_320234 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    2 * (a^3 + b^3 + c^3) / (a * b * c) + 3 ≤ 1 / a^2 + 1 / b^2 + 1 / c^2 := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have h2 : 1 / a^2 + 1 / b^2 + 1 / c^2 - (2 * (a^3 + b^3 + c^3) / (a * b * c) + 3) ≥ 0 := by
    have h3 : 0 < a^2 * b^2 * c^2 := by positivity
    have h4 : 1 / a^2 + 1 / b^2 + 1 / c^2 - (2 * (a^3 + b^3 + c^3) / (a * b * c) + 3) =
        (b^2 * c^2 + a^2 * c^2 + a^2 * b^2 - 2 * (a^3 + b^3 + c^3) * (a * b * c) - 3 * (a * b * c)^2) / (a^2 * b^2 * c^2) := by
      field_simp
      ring
    have h5 : b^2 * c^2 + a^2 * c^2 + a^2 * b^2 - 2 * (a^3 + b^3 + c^3) * (a * b * c) - 3 * (a * b * c)^2 ≥ 0 := by
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        h, sq_nonneg (a * b * c), sq_nonneg (a^2 + b^2 + c^2 - 1)
      ]
    have h6 : (b^2 * c^2 + a^2 * c^2 + a^2 * b^2 - 2 * (a^3 + b^3 + c^3) * (a * b * c) - 3 * (a * b * c)^2) / (a^2 * b^2 * c^2) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith [h4, h6]
  linarith