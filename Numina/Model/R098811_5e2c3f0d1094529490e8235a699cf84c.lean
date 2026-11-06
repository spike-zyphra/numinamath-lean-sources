import Mathlib

theorem number_theory_139009 (n m : ℤ) : 9 ∣ 2 * n + 5 * m ↔ 9 ∣ 5 * n + 8 * m := by
  constructor
  · -- Assume 9 divides 2n + 5m, prove 9 divides 5n + 8m
    intro h
    omega
  · -- Assume 9 divides 5n + 8m, prove 9 divides 2n + 5 * m
    intro h
    omega