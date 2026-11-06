import Mathlib

theorem number_theory_125529 (n : ℕ) : 3 ∣ 4^n + 5 := by 
  have h : ∀ n : ℕ, 3 ∣ 4^n + 5 := by 
    intro n 
    induction n with 
    | zero => 
      norm_num
    | succ k ih => 
      have h1 : 4 ^ (k + 1) + 5 = 3 * (4 ^ k) + (4 ^ k + 5) := by 
        ring_nf
      rw [h1]
      omega 
  exact h n