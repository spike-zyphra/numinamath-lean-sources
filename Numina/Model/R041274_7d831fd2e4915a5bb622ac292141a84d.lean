import Mathlib

theorem number_theory_178266 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : ∃ k, k^2 = n + (10 * (n % 10) + (n / 10))) :
    n = 29 ∨ n = 38 ∨ n = 47 ∨ n = 56 ∨ n = 65 ∨ n = 74 ∨ n = 83 ∨ n = 92 := by
  rcases h₂ with ⟨k, hk⟩
  have h3 : k ≤ 14 := by
    by_contra h
    push_neg at h
    have hk1 : k ^ 2 ≥ 15 ^ 2 := by
      have h6 : k ≥ 15 := by linarith
      nlinarith [show k ≥ 15 from h6]
    have h41 : k ^ 2 ≤ 198 := by
      have h421 : n + (10 * (n % 10) + (n / 10)) ≤ 198 := by
        omega
      nlinarith [hk, h421]
    nlinarith
  interval_cases k <;> try { 
    omega
  }