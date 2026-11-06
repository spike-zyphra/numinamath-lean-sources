import Mathlib

theorem number_theory_311935 (m : ℤ) :
    ∃ a b k : ℤ, ¬ 2 ∣ a ∧ ¬ 2 ∣ b ∧ k ≥ 0 ∧ a^2 + b^2 = m^2 + k := by
  use 2 * m + 1
  use 2 * m + 3
  use 7 * m ^ 2 + 16 * m + 10
  constructor
  · -- Show ¬ 2 ∣ (2 * m + 1)
    intro h
    have h1 : (2 * m + 1) % 2 = 0 := by
      omega
    omega
  constructor
  · -- Show ¬ 2 ∣ (2 * m + 3)
    intro h
    have h2 : (2 * m + 3) % 2 = 0 := by
      omega
    omega
  constructor
  · -- Show k ≥ 0
    nlinarith [sq_nonneg (m + 1 : ℤ), sq_nonneg (m + 2 : ℤ), sq_nonneg (m : ℤ)]
  · -- Show a^2 + b^2 = m^2 + k
    ring