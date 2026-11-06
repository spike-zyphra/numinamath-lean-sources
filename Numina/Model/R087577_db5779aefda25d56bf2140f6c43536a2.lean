import Mathlib

theorem number_theory_276062 (n : ℕ) :
    41 ∣ 5 * 7^(2*n + 2) + 2^(3*n) := by
  have h1 : ∀ n : ℕ, 41 ∣ 5 * 7 ^ (2 * n + 2) + 2 ^ (3 * n) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h2 : 5 * 7 ^ (2 * (n + 1) + 2) + 2 ^ (3 * (n + 1)) =
          49 * (5 * 7 ^ (2 * n + 2)) + 8 * (2 ^ (3 * n)) := by
        ring_nf
      rw [h2]
      omega
  exact h1 n