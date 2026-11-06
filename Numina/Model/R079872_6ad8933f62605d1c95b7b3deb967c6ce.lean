import Mathlib

theorem inequalities_136519 (n : ℕ) (hn : 1 ≤ n) : 2^n ≥ n + 1 := by 
  have baseCase : 2 ^ 1 ≥ 1 + 1 := by norm_num
  have inductionStep : ∀ k : ℕ, 1 ≤ k → 2 ^ k ≥ k + 1 → 2 ^ (k + 1) ≥ (k + 1) + 1 := by 
    intro k hk h_a
    have h1 : 2 ^ (k + 1) = 2 * (2 ^ k) := by ring 
    rw [h1] 
    have h2 : 2 * (2 ^ k) ≥ 2 * ((k + 1)) := by 
      linarith [h_a]
    have h3 : 2 * ((k + 1)) ≥ (k + 1) + 1 := by
      omega 
    linarith 
  exact Nat.le_induction baseCase inductionStep n hn