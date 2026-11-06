import Mathlib

theorem number_theory_255555 (a b : ℕ) : (a^2 + a * b + b^2) ∣ ((a + b)^6 - a^6) := by
  use 6 * a^3 * b + 9 * a^2 * b^2 + 5 * a * b^3 + b^4
  all_goals
    ring_nf
    <;> omega