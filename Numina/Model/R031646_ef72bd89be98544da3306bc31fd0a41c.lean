import Mathlib

theorem number_theory_604091 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : ∃ k, n = k * 100 + (k + 1) * 10 + (k + 2) + (k + 3))
    (h₂ : IsSquare (1000 * (n % 100) + 100 * ((n / 100) % 100) + 10 * ((n / 1000) % 100) + (n / 10000))) :
    n = 3456 := by
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h₃, h₄⟩
  rcases h₁ with ⟨k, hk⟩
  have h3 : k ≤ 89 := by
    omega
  interval_cases k <;> norm_num [hk] at h₂ ⊢ <;> try { 
    contrapose! h₂ 
    native_decide 
  }
  <;> omega