import Mathlib

theorem number_theory_44487 (n : ℕ) :
    1947 ∣ 46^(2 * n + 1) + 296 * 13^(2 * n + 1) := by 
  have h1 : ∀ (n : ℕ), 1947 ∣ 46 ^ (2 * n + 1) + 296 * 13 ^ (2 * n + 1) := by
    intro n 
    induction n with 
    | zero =>
      norm_num 
    | succ n ih => 
      have eq1 : 46 ^ (2 * (n + 1) + 1) + 296 * 13 ^ (2 * (n + 1) + 1) = 
        46 ^ (2 * n + 1) * 2116 + 296 * 13 ^ (2 * n + 1) * 169 := by
        ring_nf
      rw [eq1] 
      omega 
  exact h1 n