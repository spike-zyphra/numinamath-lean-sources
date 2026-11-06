import Mathlib

theorem number_theory_112260 (n : ℕ) :
  3 ∣ (2 * 7^n + 1) := by
  have h1 : ∀ n : ℕ, (2 * 7^n + 1) % 3 = 0 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ k ih =>
      have h2 : (2 * 7 ^ (k + 1) + 1) % 3 = 0 := by
        simp [pow_succ, Nat.add_mod, Nat.mul_mod] at ih ⊢
        all_goals omega
      exact h2
  exact Nat.dvd_of_mod_eq_zero (h1 n)