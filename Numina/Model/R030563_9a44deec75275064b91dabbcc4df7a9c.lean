import Mathlib

theorem algebra_187327 (x a : ℝ) (h : x ≥ 2015) (h1 : x = a) (h2 : x - 4030 + a = 0) :
    a = 2015 ↔ x = 2015 ∧ a ≠ 2015 → False := by
  have h3 : a = 2015 := by 
    have eq1 : x = a := by 
      linarith [h1]
    rw [eq1] at h2
    linarith
  have h4 : x = 2015 := by
    linarith [h1, h3]
  simp [h3, h4]
  all_goals linarith