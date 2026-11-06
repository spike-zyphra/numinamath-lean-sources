import Mathlib

theorem algebra_140499 (x : ℝ) : 8 + 5 / x + 2 / 1000 = 8.052 ↔ x = 100 := by
  constructor
  · -- Forward implication: assume the equation holds and derive x = 100
    intro h
    have h1 : x ≠ 0 := by
      by_contra h2
      rw [h2] at h
      norm_num at h
      all_goals linarith
    field_simp [h1] at h
    have h2 : x = 100 := by
      norm_num at h 
      linarith
    exact h2
  · -- Backward implication: assume x = 100 and derive the equation holds
    intro h
    rw [h]
    norm_num