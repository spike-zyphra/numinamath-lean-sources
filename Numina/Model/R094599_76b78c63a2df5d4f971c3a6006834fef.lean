import Mathlib

theorem number_theory_4040 (x y : ℕ) : 6 * x ^ 2 + 5 * y ^ 2 = 2020 ↔ False := by
  constructor
  · -- Assume 6x^2 + 5y^2 = 2020, prove False
    intro h
    have h1 : x ≤ 18 := by
      nlinarith
    have h2 : y ≤ 20 := by
      nlinarith
    interval_cases x <;> interval_cases y <;> omega
  · -- Assume False, prove anything
    intro h
    cases h