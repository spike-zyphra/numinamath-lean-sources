import Mathlib

theorem inequalities_597264 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 / (b + c) + b^2 / (c + a) + c^2 / (a + b)) ≥ (a + b + c) / 2 := by
  have h1 : 0 < b + c := by linarith
  have h2 : 0 < c + a := by linarith
  have h3 : 0 < a + b := by linarith
  have h4 : a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - (a + b + c) / 2 ≥ 0 := by
    have pos1 : 0 < (b + c) * (c + a) * (a + b) := by positivity
    have h5 : a ^ 2 / (b + c) + b ^ 2 / (c + a) + c ^ 2 / (a + b) - (a + b + c) / 2 =
        ( (2 * a ^ 2 * (c + a) * (a + b) + 2 * b ^ 2 * (b + c) * (a + b) + 2 * c ^ 2 * (b + c) * (c + a) - (a + b + c) * (b + c) * (c + a) * (a + b)) / (2 * (b + c) * (c + a) * (a + b)) ) := by
      field_simp
      ring
    rw [h5]
    apply div_nonneg
    -- Show the numerator is ≥ 0
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)),
      sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)),
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    -- Show the denominator is ≥ 0
    positivity
  linarith