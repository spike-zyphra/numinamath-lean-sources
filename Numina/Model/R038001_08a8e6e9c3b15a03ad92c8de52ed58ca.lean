import Mathlib

theorem inequalities_603065 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 1) :
    1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) + 1 / (c ^ 2 + 1) ≤ 9 / 4 := by
-- To clear denominators and move everything to the left side.

  have h1 : 0 < a * b := by
    nlinarith
  have h2 : 0 < b * c := by
    nlinarith
  have h3 : 0 < c * a := by
    nlinarith

  have h4 : 1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) + 1 / (c ^ 2 + 1) - 9 / 4 ≤ 0 := by
    have h5 : 0 < (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1) := by positivity
    have h6 : 1 / (a ^ 2 + 1) + 1 / (b ^ 2 + 1) + 1 / (c ^ 2 + 1) - 9 / 4 =
        (4 * (b ^ 2 + 1) * (c ^ 2 + 1) + 4 * (a ^ 2 + 1) * (c ^ 2 + 1) + 4 * (a ^ 2 + 1) * (b ^ 2 + 1) - 9 * (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) / (4 * (a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) := by
      field_simp
      <;> ring
    rw [h6]
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a * (b - c)), sq_nonneg (b * (a - c)), sq_nonneg (c * (a - b)),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
    positivity
  linarith