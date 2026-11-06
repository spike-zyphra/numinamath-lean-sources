import Mathlib

theorem number_theory_277975 (a b : ℕ) (h₀ : 0 ≤ a ∧ a ≤ 9) (h₁ : 0 ≤ b ∧ b ≤ 9)
    (h₂ : ∃ n, n^2 = 5000 + 100 * a + 10 * b + 4) :
    a + b = 9 := by
  rcases h₂ with ⟨n, hn⟩
  rcases h₀ with ⟨ha1, ha2⟩
  rcases h₁ with ⟨hb1, hb2⟩
  have h3 : n ≤ 77 := by
    nlinarith [sq_nonneg (n : ℕ), sq_nonneg (a : ℕ), sq_nonneg (b : ℕ),
        ha2, hb2]
  have h4 : n ≥ 71 := by
    nlinarith [sq_nonneg (n : ℕ), sq_nonneg (a : ℕ), sq_nonneg (b : ℕ),
        ha2, hb2]
  interval_cases n <;> try { 
    omega 
  } <;> try { 
    omega 
  }