import Mathlib

theorem inequalities_598356 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 ≤ 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) := by
  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb
  have hc1 : 0 < c := hc
  have h1 : 2 * a + 1 > 0 := by linarith
  have h2 : 2 * b + 1 > 0 := by linarith
  have h3 : 2 * c + 1 > 0 := by linarith

  have h4 : 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) - 1 ≥ 0 := by
    have h5 : 0 < (2 * a + 1) * (2 * b + 1) * (2 * c + 1) := by positivity
    have h7 : 1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1) - 1 =
        ( (2 * b + 1) * (2 * c + 1) + (2 * a + 1) * (2 * c + 1) + (2 * a + 1) * (2 * b + 1) - (2 * a + 1) * (2 * b + 1) * (2 * c + 1) ) / ( (2 * a + 1) * (2 * b + 1) * (2 * c + 1) ) := by
      field_simp
      <;> ring
      <;> field_simp
      <;> ring
    rw [h7] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
      habc, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
    ]
    all_goals positivity

  linarith
  all_goals positivity