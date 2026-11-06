import Mathlib

theorem number_theory_37118 {a b c d : ℤ} (h : a + b + c + d = 0) :
    ∃ x, x^2 = (a * b - c * d) * (b * c - a * d) * (c * a - b * d) := by
  have h1 : d = -a - b - c := by linarith
  use ( (a + b) * (a + c) * (b + c) )
  rw [h1]
  ring_nf