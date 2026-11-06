import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_161186 {a b : ℝ} (ha : a ≠ b) (h : -sqrt ((1 / (a - b)^2)) * (b - a) = 1)
  (x : ℝ) :
  (3 * x - 4 * a ≤ a - 2 * x ∧ (3 * x + 2 * b) / 5 > b) ↔ b < x ∧ x ≤ a := by
  constructor
  · -- Assume the system of inequalities hold, prove b < x ∧ x ≤ a
    intro h1
    rcases h1 with ⟨h1₁, h1₂⟩
    constructor
    · -- Show that b < x
      linarith
    · -- Show that x ≤ a
      linarith
  · -- Assume b < x ∧ x ≤ a, prove the system of inequalities hold
    rintro ⟨h2₁, h2₂⟩
    constructor
    · -- First inequality
      linarith
    · -- Second inequality
      linarith