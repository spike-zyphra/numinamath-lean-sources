import Mathlib

open Real

theorem inequalities_3580 (p : ℝ) (h : p ∈ Set.Icc 0 1) :
    1 - p ≤ exp (-p) := by
  rcases h with ⟨hp0, hp1⟩
  have h4 : 1 - p ≤ exp (-p) := by
    have h5 : -p + 1 ≤ exp (-p) := by
      linarith [add_one_le_exp (-p)]
    linarith
  linarith