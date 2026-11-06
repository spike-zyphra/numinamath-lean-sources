import Mathlib

theorem number_theory_305989 (t : ℕ) (ht : t > 0) :
    ∃ a b, a > 1 ∧ b > 1 ∧ 2^t = a^b + 1 ∨ 2^t = a^b - 1 ↔ t = 3 := by
  by_cases h : t = 3 
  · -- if t=3.
    use 3, 2 
    simp [h, Nat.pow_succ]
  · -- else
    use 1, 1 
    simp at h ⊢ 
    all_goals 
      try { 
        omega 
      }