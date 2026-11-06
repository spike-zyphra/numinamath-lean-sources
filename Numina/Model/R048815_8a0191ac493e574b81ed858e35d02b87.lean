import Mathlib

theorem number_theory_123940 :
    ∀ N : ℕ, ∃ m : ℕ, m > N ∧ 100 ∣ (2 ^ m + m ^ 2) := by 
  intro N
  use (100 * (N + 1) + 6)
  constructor
  · -- Show that 100 * (N + 1) + 6 > N
    linarith [show N + 1 > 0 by omega]
  · -- Show that 100 divides (2 ^ m + m ^ 2) where m = 100 * (N + 1) + 6
    have h1 : (2 : ℕ) ^ (100 * (N + 1) + 6) % 100 = 64 := by
      have h1 : ∀ k : ℕ, (2 : ℕ) ^ (100 * k + 6) % 100 = 64 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          have h2 : (2 : ℕ) ^ (100 * (k + 1) + 6) % 100 = ((2 : ℕ) ^ (100 * k + 6) * (2 ^ 100)) % 100 := by
            ring_nf
            <;> omega
          rw [h2]
          rw [Nat.mul_mod]
          rw [ih]
          norm_num
      have h1' := h1 (N + 1)
      exact h1'
    have h2 : (100 * (N + 1) + 6) ^ 2 % 100 = 36 := by
      ring_nf
      <;> omega
    have h3 : (2 ^ (100 * (N + 1) + 6) + (100 * (N + 1) + 6) ^ 2) % 100 = 0 := by
      norm_num [Nat.add_mod, h1, h2]
    exact Nat.dvd_of_mod_eq_zero h3