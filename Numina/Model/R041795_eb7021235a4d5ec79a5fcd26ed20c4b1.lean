import Mathlib

theorem number_theory_282753 (n : ℕ) :
    10^(3*n+3) + 3*10^(2*n+2) + 3*10^(n+1) + 1 = (10^(n+1) + 1)^3 := by
  ring_nf