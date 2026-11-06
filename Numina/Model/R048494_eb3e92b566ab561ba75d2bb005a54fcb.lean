import Mathlib

theorem algebra_3368 (x : ℝ) (hx : x > 0) (h : 1 / (3 * x) + 1 / (2 * x) + 1 / x = 1 / 66) :
    2 * x = 242 := by 
  have hx1 : x ≠ 0 := by linarith
  have h1 : 1 / (3 * x) + 1 / (2 * x) + 1 / x = 11 / (6 * x) := by 
    field_simp [show 3 * x ≠ 0 by
      by_contra h'
      have : x = 0 := by linarith
      contradiction, show 2 * x ≠ 0 by
        by_contra h'
        have : x = 0 := by linarith
        contradiction, show x ≠ 0 by exact hx1
        ]
    ring
  rw [h1] at h
  have hx2 : 6 * x ≠ 0 := by 
    by_contra h'
    have : x = 0 := by linarith
    contradiction
  field_simp [hx2] at h 
  nlinarith
  all_goals linarith
  all_goals linarith
  all_goals linarith