import Mathlib

theorem number_theory_5418 :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧
      ∃ a b : ℕ, n = a^2 + 25 * b^2 ∧ Nat.gcd a (5 * b) = 1 ∧
      ∃ c d e : ℕ, n = c^2 + 9 * d^2 + 16 * e^2 ∧ c > 0 ∧ d > 0 ∧ e > 0 := by
  intro N
  use 25 * (N + 1)^2 + 10 * (N + 1) + 26
  constructor
  · -- Show that n > N
    nlinarith [sq_nonneg (N + 1)]
  · -- Show the existence of a, b, c, d, e
    use 5 * (N + 1) + 1, 1
    constructor
    · -- Show n = a^2 + 25 * b^2
      ring_nf
    constructor
    · -- Show gcd(a, 5 * b) = 1
      have h1 : Nat.gcd (5 * (N + 1) + 1) (5 * 1) = 1 := by
        simp [Nat.gcd]
        all_goals omega
      exact h1
    · -- Show the existence of c, d, e
      use 5 * (N + 1) + 1, 1, 1
      constructor
      · -- Show n = c^2 + 9 * d^2 + 16 * e^2
        ring_nf
      constructor
      · -- Show c > 0
        omega
      constructor
      · -- Show d > 0
        omega
      · -- Show e > 0
        omega