import Mathlib


open Real


theorem inequalities_597500 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≥ 3 * (a + b + c)^2 := by
  have h1 : 0 ≤ a * b * c := by
    apply mul_nonneg
    apply mul_nonneg
    all_goals linarith
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a * c - 1), sq_nonneg (b * c - 1),
          sq_nonneg (a + 1), sq_nonneg (a - 1), sq_nonneg (b + 1), sq_nonneg (b - 1), sq_nonneg (c + 1), sq_nonneg (c - 1),
          sq_nonneg (a * b + a * c + b * c - 3), sq_nonneg (a * b * c - 1),
          mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]