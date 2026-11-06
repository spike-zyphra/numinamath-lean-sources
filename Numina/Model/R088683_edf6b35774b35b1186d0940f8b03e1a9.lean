import Mathlib

theorem algebra_292148 (a b : ℤ) (h₀ : a ≠ 0) (h₁ : b ≠ 0)
    (h₂ : a - b = a - (a - b)) (h₃ : b - a = b - (b - a)) :
    a - b - (a - b) - (b - a) - (a - b) - (b - a) - (a - b) - (b - a) -
    (a - b) - (b - a) - (a - b) - (b - a) = -a := by
  have eq_a : a = 2 * b := by
    linarith
  have eq_b : b = 2 * a := by
    linarith
  have h4 : b = 0 := by
    rw [eq_a] at eq_b
    linarith
  contradiction