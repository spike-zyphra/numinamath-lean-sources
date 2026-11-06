import Mathlib

theorem algebra_209692 (a b c d : ℤ) (h : a + b + c + d = 0) :
    ∃ m, m^2 = 2 * (a^4 + b^4 + c^4 + d^4) + 8 * a * b * c * d := by
  have h1 : d = -a - b - c := by linarith 
  use a^2 + b^2 + c^2 + d^2
  rw [h1] 
  ring