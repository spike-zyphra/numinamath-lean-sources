import Mathlib

theorem number_theory_199867 (n : ℕ) : 133 ∣ 11^(n + 2) + 12^(2 * n + 1) := by
  have h1 : ∀ (n : ℕ), 133 ∣ 11 ^ (n + 2) + 12 ^ (2 * n + 1) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h2 : 133 ∣ 11 ^ (n + 1 + 2) + 12 ^ (2 * (n + 1) + 1) := by
        have eq : 11 ^ (n + 1 + 2) + 12 ^ (2 * (n + 1) + 1) =
            11 * (11 ^ (n + 2)) + 144 * (12 ^ (2 * n + 1)) := by
          ring_nf
        rw [eq]
        omega
      exact h2
  specialize h1 n
  simpa using h1