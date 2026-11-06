import Mathlib

theorem number_theory_165223 (n : ℤ) : ∃ a b c d : ℤ, n = a^2 + b^2 - c^2 - d^2 := by
  by_cases h : n % 2 = 0
  · -- n is even
    have h1 : ∃ k, n = 2 * k := by
      refine' ⟨n / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    use k
    use 1
    use k - 1
    use 0
    nlinarith
  · -- n is odd
    have h1 : ∃ k, n = 2 * k + 1 := by
      refine' ⟨(n - 1) / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    use k + 1
    use 0
    use 0
    use k
    nlinarith