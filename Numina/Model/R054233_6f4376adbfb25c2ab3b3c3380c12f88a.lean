import Mathlib

theorem number_theory_170769 (n : ℕ) (h₀ : 100 < n) (h₁ : n < 200)
    (h₂ : n % 11 = 0) (h₃ : ¬Prime n) (h₄ : ∃k, n = k^2) :
    n = 121 := by 
  rcases h₄ with ⟨k, hk⟩
  have h5 : k > 10 := by
    nlinarith [hk, h₀]
  have h6 : k < 15 := by
    nlinarith [hk, h₁]
  interval_cases k <;> norm_num [hk] at *
  <;> try { trivial }
  <;> norm_num [Nat.Prime] at h₃ ⊢
  <;> all_goals contradiction