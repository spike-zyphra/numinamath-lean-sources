import Mathlib

theorem number_theory_98368 (n d : ℕ) (h₀ : 0 < n) (h₁ : 0 ≤ d ∧ d < n ∧ d ≤ 9)
    (h₂ : Nat.ofDigits n [d, 2, 3] = 263) (h₃ : Nat.ofDigits n [4, 2, 3] =
    Nat.ofDigits 6 [1, d, 1, 1]) : n + d = 11 := by
  simp [Nat.ofDigits, List.foldl] at h₂ h₃
  rcases h₁ with ⟨h₄, h₅, h₆⟩
  have h4 : n ≤ 32 := by
    by_contra h
    push_neg at h
    have eq2 : 3 * n ^ 2 + 2 * n + 4 = 253 + 6 * d := by
      nlinarith
    have eq3 : 3 * n ^ 2 + 2 * n + 4 = 253 + 6 * d := by 
      nlinarith
    have h5 : n ≤ 32 := by
       nlinarith [sq_nonneg (n : ℕ), sq_nonneg (d : ℕ), 
           sq_nonneg ((n) : ℕ), sq_nonneg ((d) : ℕ)
           ]
    omega
  have h6 : n ≤ 32 := by omega
  interval_cases n <;> try { 
    omega
  } <;> try { 
    interval_cases d <;> omega
  }