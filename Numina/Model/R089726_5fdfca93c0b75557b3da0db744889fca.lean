import Mathlib

theorem inequalities_165064
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d)
    (h : a + b + c + d = 4) :
    a * b + b * c + c * d + d * a ≤ 4 := by
  have h1 : a * b + b * c + c * d + d * a = (a + c) * (b + d) := by
    ring
  rw [h1]
  have h2 : b + d = 4 - (a + c) := by linarith
  rw [h2]
  have h3 : (a + c) * (4 - (a + c)) ≤ 4 := by
    nlinarith [sq_nonneg ((a + c) - 2)]
  nlinarith [sq_nonneg ((a + c) - 2)]