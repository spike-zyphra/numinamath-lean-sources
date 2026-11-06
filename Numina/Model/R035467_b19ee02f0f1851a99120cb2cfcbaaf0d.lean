import Mathlib

theorem number_theory_248 (n : ℕ) (h₀ : n > 0) (h₁ : ∃ k, n + 100 = k^2) (h₂ : ∃ m, n + 168 = m^2) :
    n = 156 := by 
  rcases h₁ with ⟨k, hk⟩
  rcases h₂ with ⟨m, hm⟩
  have eq1 : m ^ 2 = n + 168 := by linarith
  have eq2 : k ^ 2 = n + 100 := by linarith
  have h3 : m ^ 2 = k ^ 2 + 68 := by 
    omega
  have h4 : m > k := by
    by_contra h
    push_neg at h
    have h5 : m ^ 2 ≤ k ^ 2 := by
      nlinarith [h, sq_nonneg (m : ℕ), sq_nonneg (k : ℕ)]
    omega
  have h8 : m ≤ 34 := by
    nlinarith [sq_nonneg (m : ℕ), sq_nonneg (k : ℕ), h3, sq_nonneg ((m : ℕ) - (k : ℕ) : ℤ)]
  have h9 : k ≤ 32 := by
    nlinarith [sq_nonneg (m : ℕ), sq_nonneg (k : ℕ), h3, sq_nonneg ((m : ℕ) - (k : ℕ) : ℤ)]
  interval_cases k <;> interval_cases m <;> omega