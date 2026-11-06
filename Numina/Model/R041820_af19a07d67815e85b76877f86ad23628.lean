import Mathlib

theorem number_theory_192611 (k : ℕ) : 11 ∣ 5^(5*k+1) + 4^(5*k+2) + 3^(5*k) := by
  have h1 : ∀ (k : ℕ), 11 ∣ 5 ^ (5 * k + 1) + 4 ^ (5 * k + 2) + 3 ^ (5 * k) := by
    intro k
    induction k with
    | zero =>
      norm_num
    | succ k ih =>
      have h2 : 5 ^ (5 * (k + 1) + 1) + 4 ^ (5 * (k + 1) + 2) + 3 ^ (5 * (k + 1)) =
          5 ^ (5 * k + 6) + 4 ^ (5 * k + 7) + 3 ^ (5 * k + 5) := by
        ring_nf
      rw [h2] at *
      norm_num [Nat.pow_succ, Nat.pow_mul] at ih ⊢
      all_goals
        omega
  exact h1 k