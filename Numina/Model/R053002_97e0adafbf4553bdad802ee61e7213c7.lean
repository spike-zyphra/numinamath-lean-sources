import Mathlib

theorem number_theory_184654 (n : ℕ) (h : n > 0) :
    ∃ k, 101 ∣ n + k := by 
  use (101 - n % 101) % 101
  omega