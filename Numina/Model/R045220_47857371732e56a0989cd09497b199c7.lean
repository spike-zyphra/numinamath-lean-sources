import Mathlib

theorem number_theory_124205 (k : ℕ) :
    7 ∣ (2^(6*k+1) + 3^(6*k+1) + 5^(6*k) + 1) := by
  have h1 : ∀ k : ℕ, 7 ∣ (2^(6*k+1) + 3^(6*k+1) + 5^(6*k) + 1) := by
    intro k 
    induction k with 
    | zero => 
      norm_num 
    | succ n ih => 
      have h2 : 2^(6 * (n + 1) + 1) + 3^(6 * (n + 1) + 1) + 5^(6 * (n + 1)) + 1 =
          (2^(6 * n + 1) * 64) + (3^(6 * n + 1) * 729) + (5^(6 * n) * 15625) + 1 := by 
        ring_nf 
      rw [h2] 
      norm_num [Nat.pow_succ, Nat.mul_add] at ih ⊢ 
      all_goals omega 
  specialize h1 k 
  exact h1