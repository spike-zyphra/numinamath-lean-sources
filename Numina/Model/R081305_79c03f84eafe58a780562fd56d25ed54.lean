import Mathlib

theorem inequalities_57770 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / b + b / c + c / a ≤ a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 := by
  have pos1 : 0 < a := ha
  have pos2 : 0 < b := hb
  have pos3 : 0 < c := hc
  have h1 : a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 - (a / b + b / c + c / a) ≥ 0 := by
    have pos4 : 0 < a * b * c := by
      apply mul_pos
      apply mul_pos
      exact pos1
      exact pos2
      exact pos3
    have h2 : a ^ 2 / b ^ 2 + b ^ 2 / c ^ 2 + c ^ 2 / a ^ 2 - (a / b + b / c + c / a) =
        (a ^ 4 * c ^ 2 + b ^ 4 * a ^ 2 + c ^ 4 * b ^ 2 - (a ^ 3 * b * c ^ 2 + a ^ 2 * b ^ 3 * c + a * b ^ 2 * c ^ 3)) / (a ^ 2 * b ^ 2 * c ^ 2) := by
      field_simp
      ring
    rw [h2]
    have h3 : a ^ 4 * c ^ 2 + b ^ 4 * a ^ 2 + c ^ 4 * b ^ 2 - (a ^ 3 * b * c ^ 2 + a ^ 2 * b ^ 3 * c + a * b ^ 2 * c ^ 3) ≥ 0 := by
      nlinarith [sq_nonneg (a ^ 2 * c - b ^ 2 * a), sq_nonneg (b ^ 2 * c - c ^ 2 * b), sq_nonneg (c ^ 2 * a - a ^ 2 * b),
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        mul_pos pos1 pos2, mul_pos pos2 pos3, mul_pos pos3 pos1
        ]
    apply div_nonneg h3 (by positivity)
  linarith