import Mathlib

theorem algebra_121775 (a b : ℝ) (h : a + b = 2021) :
    ∃ x, x^2 + a * x + b = (x + 1010.5)^2 - 1010.5^2 := by
  use 1
  have hb : b = 2021 - a := by 
    linarith
  rw [hb]
  ring_nf