import Mathlib

theorem inequalities_318417 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + a + c) ≤ 1 := by

  have h1 : 0 < 1 + a + b := by
    linarith
  have h2 : 0 < 1 + b + c := by
    linarith
  have h3 : 0 < 1 + a + c := by
    linarith
  have h4 : 0 < (1 + a + b) * (1 + b + c) * (1 + a + c) := by
    positivity

  have h5 : 1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + a + c) - 1 ≤ 0 := by
    have h5 : 1 / (1 + a + b) + 1 / (1 + b + c) + 1 / (1 + a + c) - 1 =
        ( (1 + b + c) * (1 + a + c) + (1 + a + b) * (1 + a + c) + (1 + a + b) * (1 + b + c) - (1 + a + b) * (1 + b + c) * (1 + a + c) ) / ( (1 + a + b) * (1 + b + c) * (1 + a + c) ) := by
      field_simp
      <;> ring
    rw [h5] at *
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is non positive
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (a * c - 1),
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc]
    · -- Show that the denominator is non negative
      positivity

  linarith