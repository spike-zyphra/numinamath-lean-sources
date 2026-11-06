import Mathlib

theorem algebra_12578 (x : ℝ) (h : max (max (max 1 2) 3) x - min (min (min 1 2) 3) x = 1 + 2 + 3 + x) :
    x = -3 / 2 := by
  have h1 : max (max (max 1 2) 3) x = max 3 x := by
    norm_num [max_assoc, max_comm, max_left_comm]
  have h2 : min (min (min 1 2) 3) x = min 1 x := by
    norm_num [min_assoc, min_comm, min_left_comm]
  rw [h1, h2] at h
  by_cases h3 : x ≤ 3
  · -- Assume x ≤ 3
    by_cases h4 : x ≥ 1
    · -- Assume x ≥ 1
      have h5 : min 1 x = 1 := by
        apply min_eq_left
        linarith
      have h6 : max 3 x = 3 := by
        apply max_eq_left
        linarith
      rw [h5, h6] at h
      linarith
    · -- Assume x < 1
      have h5 : min 1 x = x := by
        apply min_eq_right
        linarith
      have h6 : max 3 x = 3 := by
        apply max_eq_left
        linarith
      rw [h5, h6] at h
      linarith
  · -- Assume x > 3
    have h4 : x > 3 := by linarith
    have h5 : min 1 x = 1 := by
      apply min_eq_left
      linarith
    have h6 : max 3 x = x := by
      apply max_eq_right
      linarith
    rw [h5, h6] at h
    linarith