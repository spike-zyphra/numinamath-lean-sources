import Mathlib

theorem number_theory_147598 :
    ∀ n : ℕ, ∃ a b c : ℕ,
      a > n ∧ b > n ∧ c > n ∧ a^2 + b^5 = c^3 := by
  intro n
  use (2 ^ (15 * n + 10)), (2 ^ (6 * n + 4)), (2 ^ (10 * n + 7))
  constructor
  · -- Show that a > n
    have h1 : 2 ^ (15 * n + 10) > n := by
      have h2 : ∀ (k : ℕ), 2 ^ (15 * k + 10) > k := by
        intro k
        induction k with
        | zero => 
          norm_num
        | succ k ih =>
          have h3 : 2 ^ (15 * (k + 1) + 10) = 2 ^ (15 * k + 10) * (2 ^ 15) := by
            ring_nf
          rw [h3]
          omega
      specialize h2 n
      linarith
    linarith
  constructor
  · -- Show that b > n
    have h2 : 2 ^ (6 * n + 4) > n := by
      have h3 : ∀ (k : ℕ), 2 ^ (6 * k + 4) > k := by
        intro k
        induction k with
        | zero => 
          norm_num
        | succ k ih =>
          have h4 : 2 ^ (6 * (k + 1) + 4) = 2 ^ (6 * k + 4) * (2 ^ 6) := by
            ring_nf
          rw [h4]
          omega
      specialize h3 n
      linarith
    linarith
  constructor
  · -- Show that c > n
    have h3 : 2 ^ (10 * n + 7) > n := by
      have h4 : ∀ (k : ℕ), 2 ^ (10 * k + 7) > k := by
        intro k
        induction k with
        | zero => 
          norm_num
        | succ k ih =>
          have h5 : 2 ^ (10 * (k + 1) + 7) = 2 ^ (10 * k + 7) * (2 ^ 10) := by
            ring_nf
          rw [h5]
          omega
      specialize h4 n
      linarith
    linarith
  · -- Show that a^2 + b^5 = c^3
    have h4 : (2 ^ (15 * n + 10)) ^ 2 + (2 ^ (6 * n + 4)) ^ 5 = (2 ^ (10 * n + 7)) ^ 3 := by
      ring_nf
    linarith [h4]