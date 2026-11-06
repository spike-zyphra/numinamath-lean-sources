import Mathlib

theorem number_theory_271158 (n : ℕ) : 27 ∣ 2^(5 * n + 1) + 5^(n + 2) := by
  have h1 : ∀ n : ℕ, 27 ∣ 2^(5 * n + 1) + 5^(n + 2) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h2 : 27 ∣ 2^(5 * (n + 1) + 1) + 5^(n + 1 + 2) := by
        have h3 : 2 ^ (5 * (n + 1) + 1) + 5 ^ (n + 1 + 2) =
          32 * (2 ^ (5 * n + 1)) + 5 * (5 ^ (n + 2)) := by
          ring_nf
        rw [h3]
        omega
      exact h2
  exact h1 n