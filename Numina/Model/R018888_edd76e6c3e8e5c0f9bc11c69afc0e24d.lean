import Mathlib

theorem inequalities_603187 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    4 ^ 1 ≤ 1 / a + 1 / b + 1 / c + 3 / (a + b + c) := by
  have h1 : 1 / a + 1 / b + 1 / c = a * b + a * c + b * c := by
    field_simp [(show 0 < a * b * c from by positivity), habc]
    <;> nlinarith
  rw [h1]
  have ha1 : 0 < a + b + c := by linarith
  have h2 : a * b + a * c + b * c + 3 / (a + b + c) - 4 ≥ 0 := by
    have h3 : a * b + a * c + b * c + 3 / (a + b + c) - 4 = ((a * b + a * c + b * c) * (a + b + c) + 3 - 4 * (a + b + c)) / (a + b + c) := by
      field_simp
      <;> ring
    rw [h3]
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      sq_nonneg (a * b * c - 1),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    linarith
  linarith