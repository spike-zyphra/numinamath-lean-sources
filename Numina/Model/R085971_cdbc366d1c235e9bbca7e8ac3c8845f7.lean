import Mathlib

theorem algebra_279966 (x : ℝ) (y : ℝ) (hy : 0 < y) (h : |x - Real.log y| = x + Real.log y) :
    x * (y - 1) = 0 := by
  by_cases h1 : x - Real.log y ≥ 0
  · -- Case 1: x - Real.log y ≥ 0
    rw [abs_of_nonneg h1] at h
    have h2 : Real.log y = 0 := by linarith
    have hy1 : y = 1 := by
      rw [Real.log_eq_zero] at h2
      rcases h2 with (rfl | rfl | rfl)
      all_goals linarith
    rw [hy1]
    simp
  · -- Case 2: x - Real.log y < 0
    rw [abs_of_neg (lt_of_not_ge h1)] at h
    have hx : x = 0 := by linarith
    rw [hx]
    simp