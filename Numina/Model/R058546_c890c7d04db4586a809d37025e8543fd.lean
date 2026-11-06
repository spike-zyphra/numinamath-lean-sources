import Mathlib

open Real

theorem algebra_182908 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    ((a + 1) * (b + 1) * (c + 1)) / (a * b * c + 1) ≤ 16 / 7 := by
  have h1 : 0 < a * b * c + 1 := by
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h2 : 7 * (a + 1) * (b + 1) * (c + 1) ≤ 16 * (a * b * c + 1) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
        h]
  have h3 : ((a + 1) * (b + 1) * (c + 1)) / (a * b * c + 1) ≤ 16 / 7 := by
    apply (div_le_iff₀ h1).mpr
    linarith
  exact h3