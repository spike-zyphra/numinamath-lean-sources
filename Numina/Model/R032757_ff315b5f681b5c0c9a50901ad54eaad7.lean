import Mathlib

theorem algebra_16115 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : 5 * x ^ 2 + 10 * x * y = x ^ 3 + 2 * x ^ 2 * y) :
    x = 5 := by 
  have h1 : x ^ 3 + 2 * x ^ 2 * y - 5 * x ^ 2 - 10 * x * y = 0 := by 
    linarith
  have h2 : (x ^ 2 + 2 * x * y) * (x - 5) = 0 := by
    nlinarith [h1]
  cases' (mul_eq_zero.1 h2) with h3 h4
  · -- Assume h3: x^2 + 2 * x * y = 0 
    have h5 : x ^ 2 + 2 * x * y = 0 := by
      linarith
    have h6 : x * (x + 2 * y) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.1 h6) with h7 h8 
    · -- Assume h7: x = 0
      nlinarith 
    · -- Assume h8: x + 2 * y = 0 
      nlinarith 
  · -- Assume h4: x - 5 = 0 
    linarith