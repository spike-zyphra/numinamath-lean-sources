import Mathlib

theorem algebra_193982 (n : ℕ) :
    19 ∣ 5^(2*n+1) * 2^(n+2) + 3^(n+2) * 2^(2*n+1) := by
  have h1 : ∀ n : ℕ, 19 ∣ 5^(2 * n + 1) * 2^(n + 2) + 3^(n + 2) * 2^(2 * n + 1) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have eq1 : 5 ^ (2 * (n + 1) + 1) * 2 ^ ((n + 1) + 2) + 3 ^ ((n + 1) + 2) * 2 ^ (2 * (n + 1) + 1) =
          50 * (5 ^ (2 * n + 1) * 2 ^ (n + 2)) + 12 * (3 ^ (n + 2) * 2 ^ (2 * n + 1)) := by
          ring_nf
      rw [eq1]
      omega
  exact h1 n