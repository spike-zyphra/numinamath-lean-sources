import Mathlib

theorem number_theory_160180 (n : ℕ) (hn : 2 < n) :
    Even (Nat.totient n) := by 
  apply Nat.totient_even
  linarith