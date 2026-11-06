import Mathlib

theorem number_theory_304817 (n : ℕ) (h₀ : n % 9 = 0) (h₁ : n % 11 = 0)
    (h₂ : (n / 100) % 1000 = 35) (h₃ : (n / 1000) % 9 = 0) (h₄ : (n / 10000) % 9 = 0) :
    n = 63954 := by 
  by_cases h6 : n / 100 < 1000
  · -- Case 1: n / 100 < 1000
    have h7 : n / 100 = 35 := by
      omega
    have h8 : n ≤ 3599 := by 
      omega
    have h9 : n / 1000 = 0 ∨ n / 1000 = 1 ∨ n / 1000 = 2 ∨ n / 1000 = 3 := by
      omega
    rcases h9 with (h9 | h9 | h9 | h9)
    · -- n / 1000 = 0
      have h10 : n < 1000 := by 
        omega
      omega
    · -- n / 1000 = 1
      omega
    · -- n / 1000 = 2
      omega
    · -- n / 1000 = 3
      omega
  · -- Case 2: n / 100 ≥ 1000
    have h7 : n / 100 ≥ 1000 := by 
      omega
    have h8 : n ≥ 100000 := by 
      omega
    have h9 : (n / 100) % 1000 = 35 := h₂
    have h10 : n / 100 ≥ 1000 := by
      omega
    have h11 : n / 100 = 1000 * ((n / 100) / 1000) + 35 := by 
      omega
    -- This implies n >= 100,000
    have h12 : n / 1000 = 100 * ((n / 100) / 1000) + 3 := by 
      omega
    have h13 : n / 10000 = 10 * ((n / 100) / 1000) := by 
      omega
    have h14 : (n / 1000) % 9 = 0 := h₃
    have h15 : (n / 10000) % 9 = 0 := h₄
    have h16 : (100 * ((n / 100) / 1000) + 3) % 9 = 0 := by
      have eq : n / 1000 = 100 * ((n / 100) / 1000) + 3 := h12
      rw [eq] at h14
      exact h14
    -- Substituting into h4
    have h17 : (10 * ((n / 100) / 1000)) % 9 = 0 := by
      have eq : n / 10000 = 10 * ((n / 100) / 1000) := h13
      rw [eq] at h15
      exact h15
    omega