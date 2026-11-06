import Mathlib

theorem number_theory_29026 (a b c : ℤ) (h : a + b + c = 0) :
    ∃ x, x^2 = (a^4 + b^4 + c^4) / 2 := by 
  have h1 : c = -a - b := by linarith
  rw [h1]
  use (a^2 + a * b + b^2)
  ring_nf 
  -- To results in (a^2 + ab + b^2)^2 = (a^2 + ab + b^2)^2, which trivial equal
  <;> omega