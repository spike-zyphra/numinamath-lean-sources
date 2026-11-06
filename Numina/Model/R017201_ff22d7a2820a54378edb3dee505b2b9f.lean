import Mathlib

theorem number_theory_215005 (n : ℕ) (hn : n ≥ 2) :
    ∃ x y z : ℤ, x^2 + y^2 = z^n := by 
  by_cases h : n % 2 = 0
  · -- If n is even
    have h2 : ∃ m : ℕ, n = 2 * m := by
      have : n % 2 = 0 := h
      refine' ⟨n / 2, by 
        omega⟩
    rcases h2 with ⟨m, hm⟩
    have h6 : m ≥ 1 := by 
      nlinarith [hm, hn]
    use (0 : ℤ)
    use (2 : ℤ) ^ (m : ℕ)
    use (2 : ℤ)
    rw [hm]
    have eq1 : (0 : ℤ) ^ 2 + ((2 : ℤ) ^ (m : ℕ)) ^ 2 = (2 : ℤ) ^ (2 * m : ℕ) := by
      ring_nf
    simpa using eq1
  · -- If n is odd
    have h3 : n % 2 = 1 := by 
      omega
    have h4 : ∃ m : ℕ, n = 2 * m + 1 := by 
      have : n % 2 = 1 := h3
      have : n > 0 := by linarith
      refine' ⟨(n - 1) / 2, by 
        omega⟩
    rcases h4 with ⟨m, hm⟩
    have h7 : m ≥ 1 := by 
      nlinarith [hm, hn]
    use (2 : ℤ) ^ (m : ℕ)
    use (2 : ℤ) ^ (m : ℕ)
    use (2 : ℤ)
    rw [hm]
    have eq2 : ((2 : ℤ) ^ (m : ℕ)) ^ 2 + ((2 : ℤ) ^ (m : ℕ)) ^ 2 = (2 : ℤ) ^ (2 * m + 1 : ℕ) := by
      ring_nf
    simpa using eq2