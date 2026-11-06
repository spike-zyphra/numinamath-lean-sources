import Mathlib

theorem algebra_311302 (a : ℝ) :
    ∃ x : ℝ, x^2 + x + a = 0 ∧ x^2 + a * x + 1 = 0 ↔ a = -2 := by
  use 1
  constructor
  · -- Forward direction: if both equations hold with x = 1, then a = -2
    intro h
    rcases h with ⟨h₁, h₂⟩
    linarith
  · -- Backward direction: if a = -2, then both equations hold with x = 1
    intro h
    rw [h]
    constructor <;> norm_num