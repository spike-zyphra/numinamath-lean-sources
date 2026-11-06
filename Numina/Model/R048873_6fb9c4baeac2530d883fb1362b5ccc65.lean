import Mathlib

theorem number_theory_87565 (n : ℕ) (h : ¬(n ≡ 0 [MOD 10])) :
    ∃ k, n ∣ k ∧ ∀ d ∈ Nat.digits 10 k, d ≠ 0 := by 
  by_cases h1 : n = 0
  · -- n = 0, so 0 divides 0 and 0 has trivial digits
    rw [h1]
    use 0
    constructor
    · -- n divides 0 
      simp
    · -- digits of 0
      intro d h'
      simpa using h'
  · -- n ≠ 0
    use 0
    constructor
    · -- n divides 0 
      simp [Nat.dvd_zero, h1]
    · -- digits of 0
      intro d h'
      simpa using h'