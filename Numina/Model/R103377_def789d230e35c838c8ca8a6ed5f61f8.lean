import Mathlib

theorem number_theory_51529 (a b c : ℤ) (h : a + b + c = 0) :
    ∃ x, 2*a^4 + 2*b^4 + 2*c^4 = x^2 := by 
  have h1 : c = -a - b := by linarith 
  use 2 * a^2 + 2 * a * b + 2 * b^2
  rw [h1]
  ring_nf