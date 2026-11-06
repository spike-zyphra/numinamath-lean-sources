import Mathlib

theorem number_theory_288006 (n : ℤ) : ∃ m, m^2 = n^2 + (n+1)^2 + (n * (n + 1))^2 := by
  use n^2 + n + 1
  ring_nf