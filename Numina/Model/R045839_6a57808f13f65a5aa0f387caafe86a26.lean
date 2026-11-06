import Mathlib

theorem number_theory_282304 (n : ℕ) (hn : n > 0) :
    7 ∣ 3^(2*n + 1) + 2^(n + 2) ∧
    11 ∣ 3^(2*n + 2) + 2^(6*n + 1) := by
  constructor
  · -- Show that 7 divides 3^(2*n + 1) + 2^(n + 2)
    have h1 : ∀ n : ℕ, n > 0 → 7 ∣ 3 ^ (2 * n + 1) + 2 ^ (n + 2) := by
      intro n hn
      induction n with
      | zero =>
        exfalso
        linarith
      | succ n ih =>
        cases n with
        | zero =>
          norm_num at ih ⊢
          all_goals omega
        | succ n =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals
            omega
    specialize h1 n hn
    exact h1
  · -- Show that 11 divides 3^(2*n + 2) + 2^(6*n + 1)
    have h2 : ∀ n : ℕ, n > 0 → 11 ∣ 3 ^ (2 * n + 2) + 2 ^ (6 * n + 1) := by
      intro n hn
      induction n with
      | zero =>
        exfalso
        linarith
      | succ n ih =>
        cases n with
        | zero =>
          norm_num at ih ⊢
          all_goals omega
        | succ n =>
          simp [pow_succ, pow_mul] at ih ⊢
          all_goals
            omega
    specialize h2 n hn
    exact h2