import Mathlib

theorem algebra_20472 {x : ℤ} (h : x * (x + 10) = 10 * (-10 - x)) : x = -10 := by
  have h1 : x ^ 2 + 20 * x + 100 = 0 := by
    nlinarith
  have h2 : (x + 10) ^ 2 = 0 := by
    nlinarith
  have h3 : x + 10 = 0 := by
    apply pow_eq_zero 
    exact h2
  linarith