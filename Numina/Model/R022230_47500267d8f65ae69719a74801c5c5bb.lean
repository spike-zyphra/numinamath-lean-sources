import Mathlib

theorem number_theory_7446 :
    ∀ n : ℕ, ∃ a b c : ℕ,
      a > n ∧ b > n ∧ c > n ∧
      ∃ m : ℕ, m^2 = a^2 + b^2 ∧
      ∃ p : ℕ, p^2 = a^2 + c^2 ∧
      ∃ q : ℕ, q^2 = b^2 + c^2 := by
  intro n 
  use 240 * (n + 1)
  use 117 * (n + 1)
  use 44 * (n + 1)
  constructor
  · -- Show that $a > n$
    nlinarith
  constructor
  · -- Show that $b > n$
    nlinarith
  constructor
  · -- Show that $c > n$
    nlinarith
  use 267 * (n + 1)
  constructor
  · -- Show m^2 = a^2 + b^2
    ring_nf
  use 244 * (n + 1)
  constructor
  · -- Show p^2 = a^2 + c^2
    ring_nf
  use 125 * (n + 1)
  · -- Show q^2 = b^2 + c^2
    ring_nf