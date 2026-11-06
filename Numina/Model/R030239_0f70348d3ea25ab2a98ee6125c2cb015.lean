import Mathlib

theorem number_theory_177308 :
    ∀ n : ℕ, ∃ x y z : ℕ,
      x > 0 ∧ y > n ∧ z > 0 ∧
      x^2 + 1 = y^2 + z^2 ∧
      (z^2) % 1000 = (x^2 + 1) % 1000 := by
  intro n
  use (100 * (n + 2))
  use (100 * (n + 2))
  use 1
  constructor
  · -- Show x > 0
    nlinarith
  constructor
  · -- Show y > n
    nlinarith
  constructor
  · -- Show z > 0
    omega
  constructor
  · -- Show x^2 + 1 = y^2 + z^2
    ring
  · -- Show (z^2) % 1000 = (x^2 + 1) % 1000
    ring_nf
    <;> omega