import Mathlib

theorem number_theory_107017 (n : ℕ) : 27 ∣ 10^n + 18 * n - 1 := by
  have h1 : ∀ n : ℕ, 27 ∣ 10^n + 18 * n - 1 := by
    intro n
    induction n with
    | zero =>
      use 0
      simp
    | succ n ih =>
      have h2 : 10 ^ (n + 1) + 18 * (n + 1) - 1 = 10 ^ n * 10 + 18 * (n + 1) - 1 := by
        ring_nf
      rw [h2]
      have h3 : 27 ∣ 9 * 10 ^ n + 18 := by
        have h4 : 10 ^ n % 3 = 1 := by
          have h5 : ∀ k : ℕ, (10 : ℕ) ^ k % 3 = 1 := by
            intro k
            induction k with
            | zero =>
              simp
            | succ k ih =>
              simp [Nat.pow_succ, Nat.mul_mod, ih]
          exact h5 n
        omega
      omega
  exact h1 n