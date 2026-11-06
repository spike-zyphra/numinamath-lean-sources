import Mathlib

theorem algebra_196417 (x y : ℝ) (h : (2 * x + y + 2) + (x + 2 * y) + (2 * x - y) = 3 * min (2 * x + y + 2) (min (x + 2 * y) (2 * x - y))) :
    x + y = -4 := by

  have h1 : (2 * x + y + 2) + (x + 2 * y) + (2 * x - y) = 5 * x + 2 * y + 2 := by
    linarith

  have h2 : 5 * x + 2 * y + 2 = 3 * min (2 * x + y + 2) (min (x + 2 * y) (2 * x - y)) := by
    linarith [h, h1]

  by_cases h3 : 2 * x + y + 2 ≤ min (x + 2 * y) (2 * x - y)
  · -- Case where $2x + y + 2$ is the minimum
    have h4 : min (2 * x + y + 2) (min (x + 2 * y) (2 * x - y)) = 2 * x + y + 2 := by
      apply min_eq_left h3
    rw [h4] at h2
    linarith

  · -- Case where $2x + y + 2$ is not the minimum
    have h4 : min (2 * x + y + 2) (min (x + 2 * y) (2 * x - y)) = min (x + 2 * y) (2 * x - y) := by
      apply min_eq_right
      linarith [h3]
    rw [h4] at h2

    by_cases h5 : x + 2 * y ≤ 2 * x - y
    · -- Case where `min (x + 2 * y) (2 * x - y) = x + 2 * y`
      have h6 : min (x + 2 * y) (2 * x - y) = x + 2 * y := by
        apply min_eq_left h5
      rw [h6] at h2
      linarith [h5, h2]

    · -- Case where `min (x + 2 * y) (2 * x - y) = 2 * x - y`
      have h6 : min (x + 2 * y) (2 * x - y) = 2 * x - y := by
        apply min_eq_right
        linarith [h5]
      rw [h6] at h2
      linarith [h5, h2]