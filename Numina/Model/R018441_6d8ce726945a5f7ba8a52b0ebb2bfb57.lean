import Mathlib

theorem algebra_110196 :
    ∀ n : ℕ, ∃ a b c : ℕ,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (a + b) * c = a * b ∧
      a > n ∧ b > n ∧ c > n := by
  intro n
  use 3 * (n + 1), 6 * (n + 1), 2 * (n + 1)
  constructor
  · -- Show that a ≠ b
    by_contra h
    have : 3 * (n + 1) = 6 * (n + 1) := by linarith
    have : n + 1 = 0 := by
      omega
    omega
  constructor
  · -- Show that a ≠ c
    by_contra h
    have : 3 * (n + 1) = 2 * (n + 1) := by linarith
    have : n + 1 = 0 := by
      omega
    omega
  constructor
  · -- Show that b ≠ c
    by_contra h
    have : 6 * (n + 1) = 2 * (n + 1) := by linarith
    have : n + 1 = 0 := by
      omega
    omega
  constructor
  · -- Show that (a + b) * c = a * b
    ring
  constructor
  · -- Show that a > n
    omega
  constructor
  · -- Show that b > n
    omega
  · -- Show that c > n
    omega