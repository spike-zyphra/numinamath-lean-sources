import Mathlib

theorem inequalities_45230 (a b c x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : 5 * a + 4 * b + 3 * c = 5 * x + 4 * y + 3 * z) :
    a ^ 5 / x ^ 4 + b ^ 4 / y ^ 3 + c ^ 3 / z ^ 2 ≥ x + y + z := by
  have h1 : a ^ 5 / x ^ 4 ≥ 5 * a - 4 * x := by
    have hx4_pos : 0 < x ^ 4 := by positivity
    apply (le_div_iff₀ hx4_pos).mpr
    nlinarith [sq_nonneg (a - x), sq_nonneg (a ^ 2 - a * x), sq_nonneg (a - 2 * x), sq_nonneg (x - 2 * a), sq_nonneg (a ^ 2 - x ^ 2), sq_nonneg (a * x - x ^ 2), sq_nonneg (a ^ 2 - a * x), mul_pos ha hx, sq_nonneg (a * (a - x)), sq_nonneg (x * (a - x)), sq_nonneg (a ^ 3 - x ^ 3)]
  have h2 : b ^ 4 / y ^ 3 ≥ 4 * b - 3 * y := by
    have hy3_pos : 0 < y ^ 3 := by positivity
    apply (le_div_iff₀ hy3_pos).mpr
    nlinarith [sq_nonneg (b - y), sq_nonneg (b ^ 2 - b * y), sq_nonneg (b - 2 * y), sq_nonneg (y - 2 * b), sq_nonneg (b ^ 2 - y ^ 2), sq_nonneg (b * y - y ^ 2), sq_nonneg (b ^ 2 - b * y), mul_pos hb hy, sq_nonneg (b * (b - y)), sq_nonneg (y * (b - y)), sq_nonneg (b ^ 3 - y ^ 3)]
  have h3 : c ^ 3 / z ^ 2 ≥ 3 * c - 2 * z := by
    have hz2_pos : 0 < z ^ 2 := by positivity
    apply (le_div_iff₀ hz2_pos).mpr
    nlinarith [sq_nonneg (c - z), sq_nonneg (c - 2 * z), sq_nonneg (z - 2 * c), sq_nonneg (c ^ 2 - c * z), sq_nonneg (c ^ 2 - z ^ 2), sq_nonneg (c * z - z ^ 2), sq_nonneg (c * (c - z)), sq_nonneg (z * (c - z)), mul_pos hc hz]
  have h4 : a ^ 5 / x ^ 4 + b ^ 4 / y ^ 3 + c ^ 3 / z ^ 2 ≥ (5 * a - 4 * x) + (4 * b - 3 * y) + (3 * c - 2 * z) := by
    linarith [h1, h2, h3]
  linarith [h4, h]