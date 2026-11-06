import Mathlib

theorem algebra_299577 {x : ℝ} (h : abs (1 - x) = 1 + abs x) : Real.sqrt ((x - 1)^2) = 1 - x := by
  have h1 : x ≤ 0 := by
    by_cases h2 : x ≥ 0
    · -- x ≥ 0, so |x| = x
      have h3 : abs x = x := by
        rw [abs_of_nonneg h2]
      by_cases h4 : (1 - x) ≥ 0
      · -- 1 - x ≥ 0, so |1 - x| = 1 - x
        have h5 : abs (1 - x) = 1 - x := by
          rw [abs_of_nonneg h4]
        rw [h5, h3] at h
        have h6 : x = 0 := by linarith
        linarith
      · -- 1 - x < 0, so |1 - x| = x - 1
        have h6 : abs (1 - x) = x - 1 := by
          rw [abs_of_neg (show 1 - x < 0 by linarith)]
          all_goals linarith
        rw [h6, h3] at h
        linarith
    · -- x < 0, so |x| = -x
      have h4 : abs x = -x := by
        rw [abs_of_neg (show x < 0 by linarith)]
      have h5 : abs (1 - x) = (1 - x) := by
        rw [abs_of_pos]
        linarith
        all_goals linarith
      rw [h5, h4] at h
      linarith
  have h2 : Real.sqrt ((x - 1) ^ 2) = |x - 1| := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h2]
  have h3 : x - 1 ≤ 0 := by 
    linarith
  rw [abs_of_nonpos (by linarith)]
  all_goals linarith