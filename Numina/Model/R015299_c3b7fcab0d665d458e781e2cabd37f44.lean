import Mathlib

theorem number_theory_275595 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : ∃ k, k^2 = n + (10 * (n % 10) + (n / 10))) :
    n = 29 ∨ n = 38 ∨ n = 47 ∨ n = 56 ∨ n = 65 ∨ n = 74 ∨ n = 83 ∨ n = 92 := by
  rcases h₂ with ⟨k, hk⟩
  have h3 : k ≤ 31 := by
    by_contra h
    push_neg at h
    have h4 : k ≥ 32 := by omega
    have h5 : k^2 ≥ 32^2 := by 
      have h6 : k ≥ 32 := by omega 
      nlinarith
    have h7 : k^2 ≥ 1024 := by 
      nlinarith
    have h8 : n + (10 * (n % 10) + (n / 10)) < 200 := by 
      have h90 : n < 100 := h₀ 
      omega 
    nlinarith [show n + (10 * (n % 10) + (n / 10)) < 200 from h8]
  interval_cases k <;> try { 
    omega 
  } <;> try { 
    have h9 : n ≤ 99 := by omega 
    have h10 : n ≥ 10 := by omega 
    interval_cases n <;> omega 
  }