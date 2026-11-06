import Mathlib

theorem inequalities_599520 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) ≤
    ((a + b + c) ^ 2) / (a * b + b * c + c * a) := by

  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith
  have h4 : 0 < a * b + b * c + c * a := by
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h5 : 0 < (b + c) * (c + a) * (a + b) * (a * b + b * c + c * a) := by
    positivity

  have h6 : (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) - ((a + b + c) ^ 2) / (a * b + b * c + c * a) ≤ 0 := by
    have h7 : (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) - ((a + b + c) ^ 2) / (a * b + b * c + c * a) =
        ((a + b) * (c + a) * (a + b) * (a * b + b * c + c * a) + (b + c) * (b + c) * (a + b) * (a * b + b * c + c * a) + (c + a) * (b + c) * (c + a) * (a * b + b * c + c * a) - (a + b + c) ^ 2 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b) * (a * b + b * c + c * a)) := by
      field_simp
      ring
    rw [h7] at *
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)),
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

    positivity

  linarith [h6]