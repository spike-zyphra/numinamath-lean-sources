import Mathlib
theorem algebra_610868 (a b c d e : ℝ) (h1 : 3 * a + 2 * b + 4 * d = 10) (h2 : 6 * a + 5 * b + 4 * c + 3 * d + 2 * e = 8) (h3 : a + b + 2 * c + 5 * e = 3) (h4 : 2 * c + 3 * d + 3 * e = 4) (h5 : a + 2 * b + 3 * c + d = 7) : a + b + c + d + e = 4:= by 
  linarith