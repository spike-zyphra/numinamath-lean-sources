import Mathlib

theorem number_theory_102841 :
    ∀ n : ℕ, ∃ a b : ℕ,
      a > n ∧ b > n ∧ a * Nat.gcd a b = b + Nat.lcm a b := by
  intro n
  use 2 * (n + 1)
  use 2 * (n + 1) ^ 2
  constructor
  · -- Show that a > n
    nlinarith
  constructor
  · -- Show that b > n
    nlinarith [sq_nonneg (n + 1 : ℕ), sq_pos_of_pos (show (0 : ℕ) < 2 by norm_num)]
  · -- Show that a * gcd a b = b + lcm a b
    have h1 : Nat.gcd (2 * (n + 1)) (2 * (n + 1) ^ 2) = 2 * (n + 1) := by
      simp [Nat.gcd_mul_left, pow_two, Nat.gcd_comm]
    have h2 : Nat.lcm (2 * (n + 1)) (2 * (n + 1) ^ 2) = 2 * (n + 1) ^ 2 := by
      rw [Nat.lcm]
      rw [h1]
      field_simp
      <;> ring_nf
    calc
      (2 * (n + 1)) * Nat.gcd (2 * (n + 1)) (2 * (n + 1) ^ 2)
        = (2 * (n + 1)) * (2 * (n + 1)) := by rw [h1]
      _ = 4 * (n + 1) ^ 2 := by ring
      _ = 2 * (n + 1) ^ 2 + 2 * (n + 1) ^ 2 := by ring
      _ = (2 * (n + 1) ^ 2) + Nat.lcm (2 * (n + 1)) (2 * (n + 1) ^ 2) := by 
        rw [h2]
        all_goals ring