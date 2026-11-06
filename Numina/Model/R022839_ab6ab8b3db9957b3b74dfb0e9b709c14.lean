import Mathlib

theorem number_theory_327596 (n : ℕ) : 9 ∣ (3 * n + 1) * 7^n - 1 := by
  have h1 : ∀ (n : ℕ), 9 ∣ (3 * n + 1) * 7 ^ n - 1 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ k ih =>
      norm_num [Nat.pow_succ, Nat.mul_add, Nat.add_mul] at ih ⊢
      all_goals
        ring_nf at ih ⊢
        omega
  specialize h1 n
  simpa using h1