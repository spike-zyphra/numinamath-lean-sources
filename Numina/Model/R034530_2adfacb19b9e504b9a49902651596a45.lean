import Mathlib

theorem inequalities_25853 (a b c x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (h1 : a * x + b * y ≤ b * x + c * y) (h2 : b * x + c * y ≤ c * x + a * y) :
    b ≤ c := by
  nlinarith [mul_pos hx hy, mul_pos hx ha, mul_pos hx hb, mul_pos hx hc, mul_pos hy ha, mul_pos hy hb, mul_pos hy hc, sq_nonneg (x - y), sq_nonneg (a - c), sq_nonneg (b - c)]