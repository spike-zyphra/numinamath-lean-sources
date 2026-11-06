import Mathlib

theorem number_theory_74595 (n : ℤ) :
    ∃ a b c, n = a^2 + b^2 - c^2 := by 
  by_cases h : n % 2 = 1
  · -- n is odd
    have h1 : ∃ k, n = 2 * k + 1 := by
      refine' ⟨n / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    use 0
    use k + 1
    use k
    rw [hk]
    ring_nf <;> omega
  · -- n is even
    have h1 : n % 2 = 0 := by omega
    have h2 : ∃ k, n = 2 * k := by
      refine' ⟨n / 2, by omega⟩
    rcases h2 with ⟨k, hk⟩
    use k
    use 1
    use k - 1
    rw [hk]
    ring_nf <;> omega