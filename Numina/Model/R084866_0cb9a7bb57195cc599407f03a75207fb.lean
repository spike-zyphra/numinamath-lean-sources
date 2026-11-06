import Mathlib

theorem number_theory_241373 (n : ℕ) : 7 ∣ 3^(2*n + 1) + 2^(n + 2) := by 
  have h1 : ∀ n : ℕ, 7 ∣ 3 ^ (2 * n + 1) + 2 ^ (n + 2) := by
    intro n 
    induction n with
    | zero =>
      norm_num
    | succ k ih =>
      have h2 : 3 ^ (2 * (k + 1) + 1) + 2 ^ ((k + 1) + 2) =
          9 * 3 ^ (2 * k + 1) + 2 * 2 ^ (k + 2) := by 
        ring_nf 
      rw [h2] 
      omega 
  exact h1 n