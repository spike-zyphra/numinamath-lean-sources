import Mathlib

theorem number_theory_27461 {a b : ℤ} :
    (13 ∣ 2 * a + 3 * b ↔ 13 ∣ 2 * b - 3 * a) ∧
    (13 ∣ a ^ 2 + b ^ 2 → 13 ∣ (2 * a + 3 * b) * (2 * b + 3 * a)) := by
  constructor
  · -- Forward implication for part a
    constructor
    · -- Forward direction: If 13 | 2a+3b, prove 13 | 2b-3a
      intro h
      omega
    · -- Backward direction: If 13 | 2b-3a, prove 13 | 2a+3b
      intro h
      omega
  · -- Prove part b
    intro h
    have h4 : (2 * a + 3 * b) * (2 * b + 3 * a) = 6 * (a ^ 2 + b ^ 2 ) + 13 * (a * b) := by
      ring
    rw [h4] at *
    omega