import Mathlib

theorem number_theory_276082 (n : ℕ) (hn : n > 0) :
    19 ∣ 3^(3*n + 2) + 5 * 2^(3*n + 1) := by
  have h1 : ∀ (n : ℕ), n > 0 → 19 ∣ 3^(3*n + 2) + 5 * 2^(3*n + 1) := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      exact Nat.lt_irrefl 0 hn
    | succ n ih =>
      cases n with
      | zero =>
        norm_num
      | succ n =>
        simp [pow_succ, pow_mul] at ih ⊢
        all_goals
          omega
  exact h1 n hn