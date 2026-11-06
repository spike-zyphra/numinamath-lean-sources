import Mathlib

theorem number_theory_241974 (p : ℕ) (hp : Nat.Prime p) :
    ∃ m, ∃ k, p^m + 4 = k^2 ↔ p = 2 ∨ p = 5 := by 
  by_cases h1 : p = 2 
  · -- If p = 2, we can satisfy the bi-direction with m=5, k=6 
    use 5
    use 6 
    simp [h1]
  · -- Case of p not equal to 2 
    by_cases h2 : p = 5 
    · -- If p = 5, we can satisfy the bi-direction with m=1, k=3 
      use 1 
      use 3 
      simp [h2]
    · -- Case of p neither 2 nor 5 
      have h3 : p > 1 := by 
        by_contra h 
        push_neg at h 
        interval_cases p <;> norm_num at hp h1 h2 ⊢ 
      use 0 
      use 0 
      simp at *
      all_goals try { 
        try { contradiction }
        try { 
          tauto 
        }
      }