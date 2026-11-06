import Mathlib

theorem algebra_87995
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h1 : a * (b + c) = 152)
    (h2 : b * (c + a) = 162)
    (h3 : c * (a + b) = 170) :
    a * b * c = 720 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]