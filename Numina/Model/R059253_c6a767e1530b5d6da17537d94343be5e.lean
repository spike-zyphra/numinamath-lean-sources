import Mathlib

open Real

theorem inequalities_104444 (x : ℝ) :
    (x > 1) → (x ≥ 1) ∧ ¬(∀ x : ℝ, (x ≥ 1) → (x > 1)) := by
  intro h
  constructor
  · -- Show that x ≥ 1 from x > 1.
    linarith
  · -- Show that it's not the case that ∀ x ≥ 1, x > 1
    intro h'
    have h1 := h' 1 (by norm_num)
    norm_num at h1
    all_goals linarith