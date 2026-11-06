import Mathlib

theorem number_theory_7337 (N : ℤ) (hN : 7 ∣ N) :
    7 ∣ (N / 10 - 2 * (N % 10)) := by
  omega