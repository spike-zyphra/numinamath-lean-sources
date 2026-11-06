import Mathlib

theorem number_theory_174141 (p : ℕ) (hp : Nat.Prime p) (h : Nat.Prime (2 * p + 1))
    (k : ℕ) (hk : k < 2 * p + 1) :
    ∃ m, m > 0 ∧ (k = (2 * p + 1 - m) / 2 ∨ k = m / 2) := by

  have h1 : k < 2 * p + 1 := hk
  have hp2 : p ≥ 2 := Nat.Prime.two_le hp
  by_cases hk2 : k > 0
  · -- Assume k > 0, take m = 2k, which is positive
    use 2 * k
    constructor
    · -- Show m > 0
      omega
    · -- Show second disjunction holds
      right
      omega
  · -- k ≤ 0
    have h2 : k = 0 := by
      omega
    use 2 * p + 1
    constructor
    · -- Show m > 0
      have hp4 : p ≥ 2 := hp2
      omega
    · -- Show first disjunction holds
      left
      simp [h2]
      <;> omega