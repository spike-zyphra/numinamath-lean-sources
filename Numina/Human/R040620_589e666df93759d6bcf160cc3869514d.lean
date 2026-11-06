import Mathlib

theorem number_theory_288596 (a b : ℕ) (ha : a > 0) (hb : b > 0)
    (h1 : a % b = 0) (h2 : b ≠ 0) :
    ∃ x, x > b ∧ x % b = 0 ∧ x % a = 0 := by 
  use 2 * a * b
  constructor
  · -- Show that 2 * a * b > b 
    nlinarith [mul_pos ha hb]
  constructor
  · -- Show that (2 * a * b) % b = 0
    simp [Nat.mul_mod, h1]
  · -- Show that (2 * a * b) % a = 0
    simp [Nat.mul_mod, Nat.mod_self]