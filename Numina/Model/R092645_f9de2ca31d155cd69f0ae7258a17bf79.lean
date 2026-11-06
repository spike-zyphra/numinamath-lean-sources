import Mathlib

theorem inequalities_2982
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c) :
    a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3 ≥ a ^ 2 * b * c ^ 3 + b ^ 2 * c * a ^ 3 + c ^ 2 * a * b ^ 3 := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a ^ 2 * b - b ^ 2 * c), sq_nonneg (b ^ 2 * c - c ^ 2 * a), sq_nonneg (c ^ 2 * a - a ^ 2 * b),
          sq_nonneg (a * c - b * a), sq_nonneg (b * a - c * b), sq_nonneg (c * b - a * c),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]