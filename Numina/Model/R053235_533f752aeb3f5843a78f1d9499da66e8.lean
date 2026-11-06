import Mathlib

theorem algebra_21040 (x : ℝ) (hx : x ≠ 1) : 1 / (x - 1) + 2 * x / (x - 1) = 5 ↔ x = 2 := by
  constructor
  · -- Forward direction: if the equation holds, then x = 2
    intro h
    have h1 : x - 1 ≠ 0 := by
      intro h1
      apply hx
      linarith
    have h2 : 1 / (x - 1) + 2 * x / (x - 1) = (1 + 2 * x) / (x - 1) := by
      field_simp [(show x - 1 ≠ 0 by assumption)]
      all_goals
        ring
    rw [h2] at h 
    have h3 : 1 + 2 * x = 5 * (x - 1) := by
      field_simp [(show x - 1 ≠ 0 by assumption)] at h ⊢
      linarith
    linarith
  · -- Backward direction: if x = 2, then the equation holds
    intro h
    rw [h]
    norm_num