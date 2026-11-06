import Mathlib

theorem number_theory_303053 (n : ℕ) (hn : n > 0) :
    57 ∣ 8^(2 * n + 1) + 7^(n + 2) := by 
  have h1 : ∀ m : ℕ, 57 ∣ 8 ^ (2 * (m + 1) + 1) + 7 ^ ((m + 1) + 2) := by
    intro m 
    induction m with 
    | zero =>
      norm_num 
    | succ m ih =>
      norm_num [pow_succ, pow_mul] at ih ⊢
      omega 
  have h2 := h1 (n - 1)
  have h3 : 2 * ((n - 1) + 1) + 1 = 2 * n + 1 := by 
    omega 
  have h4 : ((n - 1) + 1) + 2 = n + 2 := by 
    omega 
  rw [h3, h4] at h2 
  exact h2