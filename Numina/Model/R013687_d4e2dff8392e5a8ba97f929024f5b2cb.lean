import Mathlib

theorem algebra_91948 (n : ℕ) (hn : 0 < n) :
    ∃ p : Polynomial ℤ, p.degree ≤ n ∧ ∀ k : ℤ, Even k → 2^n ∣ p.eval k ∧ Odd k → 2^n ∣ p.eval k - 1 := by
  use 0
  constructor
  · -- Show that the degree of the zero polynomial is ≤ n
    simp [Polynomial.degree_zero, hn]
  · -- Show that for any integer k, if k is even, then 2^n ∣ 0 and k is odd leads to 2^n ∣ 0 - 1
    intro k hk
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : k % 2 = 0 := by 
      obtain ⟨m, hm⟩ := hk
      omega
    have h4 : k % 2 = 1 := by 
      obtain ⟨m, hm⟩ := h2
      omega
    omega