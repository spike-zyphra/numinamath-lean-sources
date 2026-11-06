import Mathlib

theorem number_theory_50036 :
    (∀ n : ℕ, ∃ p : ℕ, p > n ∧ ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ 3 * p + 1 = x ^ 3 - y ^ 3) ∧
    (∀ m : ℕ, ∃ q : ℕ, q > m ∧ ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ 5 * q + 1 = x ^ 3 - y ^ 3) := by
  constructor
  · -- Prove that for any natural number n, there is a natural number p > n (satisfying p exists ...).
    intro n
    use (n + 1) ^ 2 + (n + 1)
    constructor
    · -- We need to prove that p > n
      nlinarith
    · -- For existence of natural number x and y
      use n + 2, n + 1
      constructor
      · -- Show x > 0
        omega
      constructor
      · -- Show y > 0
        omega
      · -- Show 3p +1 = x^3 -y^3
        all_goals
          simp [Nat.pow_succ, Nat.mul_add]
          <;> ring_nf
          <;> omega
  · -- Prove that for any natural number m, there is a natural number q > m (satisfying q exists ...).
    intro m
    use (15 * (m + 1) ^ 2 + 3 * (m + 1))
    constructor
    · -- Show q > m
      nlinarith
    · -- For existence of natural number x and y
      use 5 * (m + 1) + 1, 5 * (m + 1)
      constructor
      · -- Show x > 0
        nlinarith
      constructor
      · -- Show y > 0
        nlinarith
      · -- Show 5p +1 = x^3 -y^3
        all_goals
          simp [Nat.pow_succ, Nat.mul_add]
          <;> ring_nf
          <;> omega