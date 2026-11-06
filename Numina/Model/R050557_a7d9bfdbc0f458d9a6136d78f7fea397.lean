import Mathlib

theorem algebra_3140 (a b c d e : ℝ)
    (h1 : a + 2 * b + 3 * c + 4 * d + 5 * e = -13)
    (h2 : 2 * a + 2 * b + 4 * c + 3 * d + e = 22)
    (h3 : 4 * a + 3 * b + 6 * c + 3 * d - 2 * e = 62)
    (h4 : a - b + c - d + e = 17) :
    a + b + c + d + e = 5 := by 
  linarith