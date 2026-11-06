import Mathlib

theorem number_theory_119065 (n : ℕ) : 17 ∣ 3 * 5^(2 * n + 1) + 2^(3 * n + 1) := by
  have h1 : ∀ n : ℕ, 17 ∣ 3 * 5 ^ (2 * n + 1) + 2 ^ (3 * n + 1) := by
    intro n
    induction n with 
    | zero =>
      norm_num
    | succ k ih =>
      have eq1 : 3 * 5 ^ (2 * (k + 1) + 1) + 2 ^ (3 * (k + 1) + 1) = 3 * 5 ^ (2 * k + 1) * 25 + 2 ^ (3 * k + 1) * 8 := by 
        ring_nf
      rw [eq1] at *
      omega
  exact h1 n