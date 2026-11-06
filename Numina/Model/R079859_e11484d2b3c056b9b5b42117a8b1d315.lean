import Mathlib

theorem number_theory_31132 (k : ℕ) (hk : 1 < k) :
    ∃ n, k ∣ n ∧ n < k ^ 4 ∧ (Nat.digits 10 n).toFinset.card ≤ 4 := by
  use 0 
  constructor
  · 
    simp
  constructor
  · 
    have hk1 : k ≥ 2 := by linarith
    have h1 : 0 < k ^ 4 := by 
      have hk2 : k > 0 := by linarith 
      have h4 : k ^ 4 > 0 := by 
        apply Nat.pow_pos 
        linarith 
      linarith 
    linarith 
  · 
    simp