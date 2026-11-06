import Mathlib

theorem number_theory_197833 (n : ℕ) (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : ∃ k, n + (10 * (n % 10) + (n / 10)) = k ^ 2) :
    n = 29 ∨ n = 38 ∨ n = 47 ∨ n = 56 ∨ n = 65 ∨ n = 74 ∨ n = 83 ∨ n = 92 := by
  rcases h₂ with ⟨k, hk⟩
  have h3 : n < 100 := h₀
  have h4 : n > 9 := h₁
  have h5 : k ^ 2 ≤ 198 := by
    have h6 : n + (10 * (n % 10) + (n / 10)) < 200 := by
      omega
    have : k ^ 2 < 200 := by 
      linarith [hk]
    have h8 : k ^ 2 ≤ 199 := by omega
    omega

  have h6 : k ≤ 14 := by
    nlinarith

  interval_cases k <;> try { 
    norm_num at hk
    interval_cases n <;> omega
  }
  all_goals 
    omega