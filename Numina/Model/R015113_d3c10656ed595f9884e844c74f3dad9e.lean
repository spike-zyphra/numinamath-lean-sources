import Mathlib

theorem number_theory_25255 :
    ∀ n : ℕ, ∃ x y z : ℤ,
      x > n ∧ y > n ∧ z > n ∧ x^3 + y^4 = z^31 := by
  intro n
  use (2 ^ (124 * n + 72) : ℤ)
  use (2 ^ (93 * n + 54) : ℤ)
  use (2 ^ (12 * n + 7) : ℤ)
  constructor
  · -- Show x > n
    have h1 : (2 : ℤ) ^ (124 * n + 72) > (n : ℤ) := by
      have h4 : ∀ (n : ℕ), (2 : ℤ) ^ (124 * n + 72) > (n : ℤ) := by
        intro n
        induction n with
        | zero =>
          norm_num
        | succ n ih =>
          have h1 : (2 : ℤ) ^ (124 * (n + 1) + 72) = (2 : ℤ) ^ (124 * n + 72) * (2 ^ 124 : ℤ) := by
            ring_nf
          rw [h1] at *
          omega
      specialize h4 n
      linarith
    linarith
  constructor
  · -- Show y > n
    have h2 : (2 : ℤ) ^ (93 * n + 54) > (n : ℤ) := by
      have h4 : ∀ (n : ℕ), (2 : ℤ) ^ (93 * n + 54) > (n : ℤ) := by
        intro n
        induction n with
        | zero =>
          norm_num
        | succ n ih =>
          have h1 : (2 : ℤ) ^ (93 * (n + 1) + 54) = (2 : ℤ) ^ (93 * n + 54) * (2 ^ 93 : ℤ) := by
            ring_nf
          rw [h1] at *
          omega
      specialize h4 n
      linarith
    linarith
  constructor
  · -- Show z > n
    have h3 : (2 : ℤ) ^ (12 * n + 7) > (n : ℤ) := by
      have h4 : ∀ (n : ℕ), (2 : ℤ) ^ (12 * n + 7) > (n : ℤ) := by
        intro n
        induction n with
        | zero =>
          norm_num
        | succ n ih =>
          have h1 : (2 : ℤ) ^ (12 * (n + 1) + 7) = (2 : ℤ) ^ (12 * n + 7) * (2 ^ 12 : ℤ) := by
            ring_nf
          rw [h1] at *
          omega
      specialize h4 n
      linarith
    linarith
  · -- Show x^3 + y^4 = z^31
    ring_nf