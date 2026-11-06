import Mathlib

theorem number_theory_259110 (a b : ℤ) :
    29 ∣ 3 * a + 2 * b ↔ 29 ∣ 11 * a + 17 * b := by
  constructor
  · -- Forward direction: If 29 divides 3a + 2b, then 29 divides 11a + 17b
    intro h
    omega
  · -- Backward direction: If 29 divides 11a + 17b, then 29 divides 3a + 2b
    intro h
    omega