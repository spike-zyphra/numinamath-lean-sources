import Mathlib

theorem algebra_140206 {n : ℕ} (hn : n ≠ 0) :
    ∃ k, k^2 = n^4 + 2 * n^3 + 5 * n^2 + 12 * n + 5 ↔ n = 1 ∨ n = 2 := by 
  by_cases h : n ≤ 2
  · 
    interval_cases n <;> 
      try { 
        use 5 
        all_goals 
        omega 
      }
    <;> 
      try { 
        use 9 
        all_goals 
        omega 
      }
  · 
    have h1 : n > 2 := by omega 
    use 0 
    constructor 
    · -- Assume k^2 = P(n), then n = 1 or n = 2 
      intro h_eq 
      have h2 : n ^ 4 + 2 * n ^ 3 + 5 * n ^ 2 + 12 * n + 5 = 0 := by 
        nlinarith 
      have h3 : n ^ 4 + 2 * n ^ 3 + 5 * n ^ 2 + 12 * n + 5 > 0 := by 
        have : n > 0 := by 
          omega 
        nlinarith 
      linarith 
    · -- Assume n = 1 or n = 2 
      intro h_eq 
      cases h_eq with 
      | inl h_eq1 => 
        omega 
      | inr h_eq2 => 
        omega