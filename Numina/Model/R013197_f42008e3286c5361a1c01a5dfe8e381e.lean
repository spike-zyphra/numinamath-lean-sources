import Mathlib

theorem number_theory_6935 :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ ¬ Nat.Prime (n ^ 2 + n + 1) ∧ ¬ Nat.Prime (n ^ 2 + 3 * n + 3) := by
  intro N
  use 21 * N + 22
  constructor
  · -- Show that n > N
    nlinarith
  constructor
  · -- Show that ¬ Nat.Prime (n ^ 2 + n + 1)
    have h1 : ¬ Nat.Prime ((21 * N + 22) ^ 2 + (21 * N + 22) + 1) := by
      have h2 : (21 * N + 22) ^ 2 + (21 * N + 22) + 1 = 3 * (147 * N ^ 2 + 315 * N + 169) := by
        ring_nf
      rw [h2]
      have h3 : ¬ Nat.Prime (3 * (147 * N ^ 2 + 315 * N + 169)) := by
        apply Nat.not_prime_mul (by norm_num)
        all_goals
        have h4 : 147 * N ^ 2 + 315 * N + 169 ≥ 169 := by
          nlinarith [sq_nonneg (N : ℕ)]
        have h5 : 147 * N ^ 2 + 315 * N + 169 ≥ 2 := by
          nlinarith
        all_goals
          nlinarith
      exact h3
    exact h1
  · -- Show that ¬ Nat.Prime (n ^ 2 + 3 * n + 3)
    have h1 : ¬ Nat.Prime ((21 * N + 22) ^ 2 + 3 * (21 * N + 22) + 3) := by
      have h2 : (21 * N + 22) ^ 2 + 3 * (21 * N + 22) + 3 = 7 * (63 * N ^ 2 + 141 * N + 79) := by
        ring_nf
      rw [h2]
      have h3 : ¬ Nat.Prime (7 * (63 * N ^ 2 + 141 * N + 79)) := by
        apply Nat.not_prime_mul (by norm_num)
        all_goals
        have h4 : 63 * N ^ 2 + 141 * N + 79 ≥ 79 := by
          nlinarith [sq_nonneg (N : ℕ)]
        have h5 : 63 * N ^ 2 + 141 * N + 79 ≥ 2 := by
          nlinarith
        all_goals
          nlinarith
      exact h3
    exact h1