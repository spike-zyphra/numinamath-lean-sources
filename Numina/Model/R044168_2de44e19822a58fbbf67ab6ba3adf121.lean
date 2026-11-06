import Mathlib

theorem number_theory_4690 (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ∃ n x y : ℕ, 0 < n ∧ 0 < x ∧ 0 < y ∧ p ^ n = x ^ 3 + y ^ 3 ↔ p = 2 ∨ p = 3 := by 
  by_cases h1 : p = 2 
  · -- If p = 2, we can take n = 1, x = 1, y = 1 
    use 1, 1, 1 
    simp [h1] 
  · -- If p ≠ 2 
    by_cases h2 : p = 3 
    · -- If p = 3, we can take n = 2, x = 1, y = 2 
      use 2, 1, 2 
      simp [h2] 
      all_goals norm_num 
    · -- If p ≠ 2 and p ≠ 3 
      use 1, 1, 1 
      simp at *
      all_goals 
        try { 
          tauto 
        } 
        <;> try { 
          norm_num at *
          all_goals try { 
            tauto 
          } 
        }