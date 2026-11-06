import Mathlib

open Function

theorem number_theory_608702 : ∃ (f : ℕ → ℝ), ∀ (v : ℕ), 1 ≤ v → (∃ t, (t > 0) ∧  f t = v * t) := by
  use fun t => ((t : ℝ) )^2
  intro v hv
  use v
  constructor
  · -- Show that t > 0
    omega
  · -- Show that f v = v * v
    simp [pow_two]
    <;> ring