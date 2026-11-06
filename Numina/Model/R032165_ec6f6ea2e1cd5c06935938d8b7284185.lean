import Mathlib

theorem number_theory_276074 (n : ℕ) : 23 ∣ 5^(2*n+1) + 2^(n+4) + 2^(n+1) := by
  have h1 : ∀ n : ℕ, 23 ∣ 5 ^ (2 * n + 1) + 2 ^ (n + 4) + 2 ^ (n + 1) := by
    intro n 
    induction n with 
    | zero =>
      norm_num
    | succ n ih =>
      have eq2 : 5 ^ (2 * (n + 1) + 1) + 2 ^ ((n + 1) + 4) + 2 ^ ((n + 1) + 1) =
          25 * (5 ^ (2 * n + 1)) + 2 * (2 ^ (n + 4)) + 2 * (2 ^ (n + 1)) := by
        ring_nf
      rw [eq2] at *
      omega
  exact h1 n