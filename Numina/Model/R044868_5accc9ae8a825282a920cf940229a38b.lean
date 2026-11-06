import Mathlib

theorem inequalities_213780 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a + b) * (b + c) * (c + a) ≥ 4 * (a + b + c - 1) := by
  have h2 : (a + b) * (b + c) * (c + a) - 4 * (a + b + c - 1) ≥ 0 := by
    have h3 : (a + b) * (b + c) * (c + a) - 4 * (a + b + c - 1) =
        a^2 * b + a^2 * c + b^2 * a + b^2 * c + c^2 * a + c^2 * b + 2 * (a * b * c) - 4 * (a + b + c) + 4 := by
      nlinarith
    rw [h3]
    have h4 : a * b * c = 1 := habc
    rw [h4]
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
      sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  linarith