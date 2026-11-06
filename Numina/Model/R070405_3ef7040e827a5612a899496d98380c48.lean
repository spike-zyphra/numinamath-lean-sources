import Mathlib

theorem number_theory_270003 (a b : ℤ) : 13 ∣ 2 * a + 3 * b ↔ 13 ∣ 2 * b - 3 * a := by
  constructor
  · -- Assume 13 divides 2a + 3b, prove 13 divides 2b - 3a
    intro h
    omega
  · -- Assume 13 divides 2b - 3a, prove 13 divides 2a + 3b
    intro h
    omega