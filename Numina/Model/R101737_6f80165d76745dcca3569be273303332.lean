import Mathlib

theorem algebra_163219 (a b c d : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a > b) (h2 : b > c) (h3 : c > d) (h4 : a + b + c + d = 2004) (h5 : a^2 - b^2 + c^2 - d^2 = 2004) :
    a ≥ 503 := by
  have h6 : d = 2004 - a - b - c := by linarith
  rw [h6] at h5
  nlinarith [sq_nonneg (a - 503), sq_nonneg (b - 502), sq_nonneg (c - 501), sq_nonneg (d - 500),
    mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3)]