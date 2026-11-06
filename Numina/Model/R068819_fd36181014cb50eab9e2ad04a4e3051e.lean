import Mathlib

theorem inequalities_599822
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d)
    (h : a + b + c + d = 1) :
    a * b + b * c + c * d + d * a ≤ 1 / 4 := by 
  have h1 : a * b + b * c + c * d + d * a = (b + d) * (a + c) := by
    ring
  rw [h1]
  have h3 : (b + d) + (a + c) = 1 := by 
    linarith [h]
  nlinarith [sq_nonneg ((b + d) - 1 / 2)]