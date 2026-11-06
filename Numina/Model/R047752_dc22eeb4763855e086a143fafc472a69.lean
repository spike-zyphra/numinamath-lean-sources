import Mathlib

theorem inequalities_327543 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (f : ℝ) (hf : f = (2 * a + b + c)^2 / (2 * a^2 + (b + c)^2) +
      (2 * b + c + a)^2 / (2 * b^2 + (c + a)^2) +
      (2 * c + a + b)^2 / (2 * c^2 + (a + b)^2)) :
    f ≤ 8 := by
  rw [hf]
  have h1 : 0 < (2 * a^2 + (b + c) ^ 2) * (2 * b^2 + (c + a) ^ 2) * (2 * c^2 + (a + b) ^ 2) := by positivity
  have h : (2 * a + b + c) ^ 2 / (2 * a^2 + (b + c) ^ 2) +
      (2 * b + c + a) ^ 2 / (2 * b^2 + (c + a) ^ 2) +
      (2 * c + a + b) ^ 2 / (2 * c^2 + (a + b) ^ 2) - 8 ≤ 0 := by
    have eq : (2 * a + b + c) ^ 2 / (2 * a^2 + (b + c) ^ 2) +
        (2 * b + c + a) ^ 2 / (2 * b^2 + (c + a) ^ 2) +
        (2 * c + a + b) ^ 2 / (2 * c^2 + (a + b) ^ 2) - 8 =
        ((2 * a + b + c) ^ 2 * (2 * b^2 + (c + a) ^ 2) * (2 * c^2 + (a + b) ^ 2) +
        (2 * b + c + a) ^ 2 * (2 * a^2 + (b + c) ^ 2) * (2 * c^2 + (a + b) ^ 2) +
        (2 * c + a + b) ^ 2 * (2 * a^2 + (b + c) ^ 2) * (2 * b^2 + (c + a) ^ 2) - 8 * (2 * a^2 + (b + c) ^ 2) * (2 * b^2 + (c + a) ^ 2) * (2 * c^2 + (a + b) ^ 2)) / ((2 * a^2 + (b + c) ^ 2) * (2 * b^2 + (c + a) ^ 2) * (2 * c^2 + (a + b) ^ 2)) := by
      field_simp
      ring
    rw [eq]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show Numerator is ≤ 0
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)),
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    · -- Show Denominator is ≥ 0
      positivity
  linarith