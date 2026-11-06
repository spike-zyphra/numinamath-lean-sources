import Mathlib

theorem number_theory_168418 (a b : ℤ) :
    7 ∣ (10 * a + b) ↔ 7 ∣ (a - 2 * b) := by
  constructor
  · -- Assume 7 divides 10 * a + b, prove 7 divides a - 2 * b
    rintro h
    have h1 : (10 * a + b) % 7 = 0 := by
      omega
    have h2 : (a - 2 * b) % 7 = 0 := by
      omega
    omega
  · -- Assume 7 divides a - 2 * b, prove 7 divides 10 * a + b
    rintro h
    have h1 : (a - 2 * b) % 7 = 0 := by
      omega
    have h2 : (10 * a + b) % 7 = 0 := by
      omega
    omega