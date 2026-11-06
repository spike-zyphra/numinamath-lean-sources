import Mathlib

theorem algebra_163965 (a b c x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h1 : a^2 + b^2 + c^2 = 25) (h2 : x^2 + y^2 + z^2 = 36)
    (h3 : a * x + b * y + c * z = 30) :
    (a + b + c) / (x + y + z) = 5 / 6 := by
  have h4 : 0 < x + y + z := by
    nlinarith [hx, hy, hz]
  have h5 : (a - 5 / 6 * x) ^ 2 + (b - 5 / 6 * y) ^ 2 + (c - 5 / 6 * z) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 5 / 6 * x), sq_nonneg (b - 5 / 6 * y), sq_nonneg (c - 5 / 6 * z)]
  have h6 : a - 5 / 6 * x = 0 := by
    nlinarith [sq_nonneg (a - 5 / 6 * x), sq_nonneg (b - 5 / 6 * y), sq_nonneg (c - 5 / 6 * z),
      h5]
  have h7 : b - 5 / 6 * y = 0 := by
    nlinarith [sq_nonneg (a - 5 / 6 * x), sq_nonneg (b - 5 / 6 * y), sq_nonneg (c - 5 / 6 * z),
      h5]
  have h8 : c - 5 / 6 * z = 0 := by
    nlinarith [sq_nonneg (a - 5 / 6 * x), sq_nonneg (b - 5 / 6 * y), sq_nonneg (c - 5 / 6 * z),
      h5]
  have h9 : a = 5 / 6 * x := by linarith
  have h10 : b = 5 / 6 * y := by linarith
  have h11 : c = 5 / 6 * z := by linarith
  have h12 : a + b + c = 5 / 6 * (x + y + z) := by
    linarith [h9, h10, h11]
  have h13 : x + y + z ≠ 0 := by
    nlinarith [hx, hy, hz]
  field_simp [h13]
  nlinarith [h12, h13]