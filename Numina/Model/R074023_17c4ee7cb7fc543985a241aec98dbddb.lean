import Mathlib

theorem number_theory_156834 (n : ℕ) : 5 ∣ 2^(3*n + 5) + 3^(n + 1) := by
  have h : ∀ n : ℕ, 5 ∣ 2 ^ (3 * n + 5) + 3 ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ k ih =>
      have h1 : 2 ^ (3 * (k + 1) + 5) + 3 ^ ((k + 1) + 1) = 8 * (2 ^ (3 * k + 5)) + 3 * (3 ^ (k + 1)) := by
        ring_nf
      rw [h1]
      omega
  exact h n