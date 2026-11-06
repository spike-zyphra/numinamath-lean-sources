import Mathlib

open Real Finset


theorem algebra_16765
    (a b c x y z : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : a^2 + b^2 + c^2 = 25)
    (h2 : x^2 + y^2 + z^2 = 36)
    (h3 : a * x + b * y + c * z = 30) :
    (a + b + c) / (x + y + z) = 5 / 6 := by
  have h4 : (a - 5/6 * x) ^2 + (b - 5/6 * y) ^2 + (c - 5/6 * z) ^2 = 0 := by
    nlinarith [sq_nonneg (a * y - b * x), sq_nonneg (b * z - c * y), sq_nonneg (c * x - a * z),
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hx, mul_pos ha hy, mul_pos ha hz,
      mul_pos hb hc, mul_pos hb hx, mul_pos hb hy, mul_pos hb hz,
      mul_pos hc hx, mul_pos hc hy, mul_pos hc hz,
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have h5 : a - 5 / 6 * x = 0 := by
    nlinarith [sq_nonneg (a - 5 / 6 * x), sq_nonneg (b - 5 / 6 * y), sq_nonneg (c - 5 / 6 * z), h4]
  have h6 : b - 5 / 6 * y = 0 := by
    nlinarith [sq_nonneg (a - 5 / 6 * x), sq_nonneg (b - 5 / 6 * y), sq_nonneg (c - 5 / 6 * z), h4]
  have h7 : c - 5 / 6 * z = 0 := by
    nlinarith [sq_nonneg (a - 5 / 6 * x), sq_nonneg (b - 5 / 6 * y), sq_nonneg (c - 5 / 6 * z), h4]
  have ha1 : a = 5 / 6 * x := by
    linarith
  have hb1 : b = 5 / 6 * y := by
    linarith
  have hc1 : c = 5 / 6 * z := by
    linarith
  have h7 : a + b + c = 5 / 6 * (x + y + z) := by
    have h8 : a + b + c = 5 / 6 * x + 5 / 6 * y + 5 / 6 * z := by
      rw [ha1, hb1, hc1]
      all_goals linarith
    linarith
  have hx1 : x + y + z > 0 := by
    linarith
  have h8 : (a + b + c) / (x + y + z) = 5 / 6 := by
    have hx2 : x + y + z ≠ 0 := by
      linarith
    rw [h7]
    field_simp [hx2]
    <;> ring
  exact h8