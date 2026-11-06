import Mathlib

theorem inequalities_603046 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 ≤ 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) := by

  have pos1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have pos2 : a * b * c = 1 := habc

  have h1 : 0 < 1 + 2 * a := by linarith
  have h2 : 0 < 1 + 2 * b := by linarith
  have h3 : 0 < 1 + 2 * c := by linarith

  have h4 : 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1 ≥ 0 := by
    have h5 : 1 / (1 + 2 * a) + 1 / (1 + 2 * b) + 1 / (1 + 2 * c) - 1 =
         ( (1 + 2 * b) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * c) + (1 + 2 * a) * (1 + 2 * b) - (1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c) ) / ((1 + 2 * a) * (1 + 2 * b) * (1 + 2 * c)) := by
      field_simp
      <;> ring
    rw [h5]
    apply div_nonneg
    -- The numerator should be ≥ 0.
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    -- Show that the denominator is positive.
    positivity
  linarith