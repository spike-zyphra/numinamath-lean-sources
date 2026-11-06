import Mathlib

theorem number_theory_217211 (n : ℕ) : 3 ∣ (2 * 7 ^ n + 1) ∧ 7 ∣ (3 ^ (2 * n + 1) + 2 ^ (n + 2)) := by
  constructor
  · -- First part: Prove that $2 \cdot 7^{n}+1$ is divisible by 3 for any natural $n$.
    have h1 : ∀ n : ℕ, 3 ∣ (2 * 7 ^ n + 1) := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ k ih =>
        norm_num [pow_succ] at ih ⊢
        all_goals omega
    exact h1 n
  · -- Second part: Prove that $3^{2n+1}+2^{n+2}$ is divisible by 7 for any natural $n$.
    have h2 : ∀ n : ℕ, 7 ∣ (3 ^ (2 * n + 1) + 2 ^ (n + 2)) := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ k ih =>
        norm_num [pow_succ, pow_mul] at ih ⊢
        all_goals omega
    exact h2 n