import Mathlib

theorem algebra_132802 (x : ℝ) (h : Real.cos (2 * x) + Real.cos (3 * x) = 1) :
    2 * Real.sin (2 * x) + 2 * Real.sin (3 * x) = Real.sin (4 * x) + 2 * Real.sin (5 * x) + Real.sin (6 * x) := by
  have h1 : Real.sin (4 * x) = 2 * Real.sin (2 * x) * Real.cos (2 * x) := by
    have h2 : 4 * x = 2 * (2 * x) := by ring
    rw [h2]
    rw [Real.sin_two_mul]
  have h2 : Real.sin (5 * x) = Real.sin (2 * x) * Real.cos (3 * x) + Real.cos (2 * x) * Real.sin (3 * x) := by
    have h3 : 5 * x = 2 * x + 3 * x := by ring
    rw [h3]
    rw [Real.sin_add]
    all_goals ring
  have h3 : Real.sin (6 * x) = 2 * Real.sin (3 * x) * Real.cos (3 * x) := by
    have h4 : 6 * x = 2 * (3 * x) := by ring
    rw [h4]
    rw [Real.sin_two_mul]
  rw [h1, h2, h3]
  have eq2 : 2 * Real.sin (2 * x) * Real.cos (2 * x) + 2 * (Real.sin (2 * x) * Real.cos (3 * x) + Real.cos (2 * x) * Real.sin (3 * x)) + 2 * Real.sin (3 * x) * Real.cos (3 * x) = 2 * (Real.sin (2 * x) + Real.sin (3 * x)) := by
    have h5 : Real.cos (2 * x) + Real.cos (3 * x) = 1 := h
    have eq3 : 2 * Real.sin (2 * x) * Real.cos (2 * x) + 2 * (Real.sin (2 * x) * Real.cos (3 * x) + Real.cos (2 * x) * Real.sin (3 * x)) + 2 * Real.sin (3 * x) * Real.cos (3 * x) = 2 * (Real.sin (2 * x) + Real.sin (3 * x)) * (Real.cos (2 * x) + Real.cos (3 * x)) := by
      ring
    rw [eq3]
    rw [h5]
    all_goals ring
  linarith [eq2]