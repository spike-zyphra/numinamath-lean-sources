import Mathlib

theorem number_theory_200323 (x y : ℕ) (h : x * 7 + y * 9 = 997) :
    ∃ k, x = 136 - 9 * k ∧ y = 7 * k + 5 := by
  have h1 : x ≤ 142 := by
    omega
  have h2 : y ≤ 110 := by
    omega
  have h5 : y ≥ 5 := by
    omega
  have h6 : (y - 5) % 7 = 0 := by
    omega
  use (y - 5) / 7
  constructor
  · -- Prove x = 136 - 9 * k
    omega
  · -- Prove y = 7 * k + 5
    omega