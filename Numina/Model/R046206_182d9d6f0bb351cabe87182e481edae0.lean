import Mathlib

theorem number_theory_87573 (n : ℤ) :
    ∃ a b c : ℤ, n = a^2 + b^2 - c^2 := by
  by_cases h : n % 2 = 1
  · -- If n is odd, then n = 2k + 1 for some integer k
    have h1 : ∃ k, n = 2 * k + 1 := by
      refine' ⟨(n - 1) / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    use k + 1, 0, k
    rw [hk]
    ring_nf
  · -- If n is even, then n = 2k for some integer k
    have h2 : n % 2 = 0 := by omega
    have h1 : ∃ k, n = 2 * k := by
      refine' ⟨n / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    use k, 1, k - 1
    rw [hk]
    ring_nf