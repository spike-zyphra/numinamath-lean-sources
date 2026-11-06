import Mathlib

theorem number_theory_3367 (n : ℕ) (h₀ : ∃ k, n = k^2) (h₁ : n < 1000000) (h₂ : n > 99999)
    (h₃ : ∃ d, d ≠ 0 ∧ n % 10 = d ∧ n / 10 % 10 = d ∧ n / 100 % 10 = d) :
    (n / 10) % 10 = 4 := by 
  rcases h₀ with ⟨k, rfl⟩
  rcases h₃ with ⟨d, hd_ne_zero, h1, h2, h3⟩
  have h4 : k ^ 2 % 10 = d := by
    omega
  have h5 : k ^ 2 / 10 % 10 = d := by
    omega
  have h6 : k ^ 2 / 100 % 10 = d := by
    omega
  have h7 : k < 1000 := by
    nlinarith
  have h8 : k > 316 := by
    nlinarith
  interval_cases k <;> norm_num at h4 h5 h6 h1 h2 h3 ⊢
    <;> omega