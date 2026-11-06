import Mathlib

theorem number_theory_144030 (n : ℕ) (hn : n = 1000000) :
    ∃ k : ℕ, k > 0 ∧ (Nat.digits 7 n).length = k ∧
      (∀ i ∈ Finset.range k, (Nat.digits 7 n)[i]! > 0) ∧
      (∀ i ∈ Finset.range k, (Nat.digits 7 n)[i]! ≤ 6 * (Nat.digits 7 n)[i - 1]!) := by 
  rw [hn]
  use 8
  constructor
  · norm_num 
  constructor 
  · native_decide 
  constructor
  · -- ∀ i ∈ Finset.range 8, (Nat.digits 7 1000000)[i]! > 0
    intro i hi
    have h1 : i < 8 := by 
      simp at hi ⊢ 
      omega 
    interval_cases i <;> norm_num at *
    all_goals 
      try { 
        native_decide 
      }
  · -- ∀ i ∈ Finset.range 8, (Nat.digits 7 1000000)[i]! ≤ 6 * (Nat.digits 7 1000000)[i - 1]! 
    intro i hi 
    have h1 : i < 8 := by 
      simp at hi ⊢ 
      omega 
    have h3 : i - 1 < 8 := by 
      omega 
    interval_cases i <;> norm_num at *
    all_goals 
      try { 
        native_decide 
      }