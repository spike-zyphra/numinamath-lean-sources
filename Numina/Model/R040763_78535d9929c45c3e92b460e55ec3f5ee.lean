import Mathlib

theorem number_theory_288641 (n : ℤ) : ∃ x y z, n = x^2 + y^2 - z^2 := by
  by_cases h : n % 2 = 0
  · -- If n is even, construct the witness
    have h1 : ∃ k, n = 2 * k := by
      refine ⟨n / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    use 1
    use -k
    use 1 - k
    rw [show n = 2 * k by linarith]
    ring
  · -- If n is odd
    have h2 : n % 2 = 1 := by
      omega
    have h1 : ∃ k, n = 2 * k + 1 := by
      have : n % 2 = 1 := h2
      refine ⟨(n - 1) / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    use 0
    use k + 1
    use k
    rw [show n = 2 * k + 1 by linarith]
    ring