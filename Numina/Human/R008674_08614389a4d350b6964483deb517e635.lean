import Mathlib

/- Jamie has a jar of coins containing the same number of nickels, dimes and quarters. The total value of the coins in the jar is $\$$13.20. How many nickels does Jamie have? -/
theorem algebra_12558 {n d q : ℕ} (h : n = d ∧ d = q) (h' : 5*n+10*d+25*q=1320) :
    n = 33 := by
  rw [h.1, h.2] at h'
  omega