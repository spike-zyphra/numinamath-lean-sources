import Mathlib

theorem algebra_12560 (x : ℝ) (h : max (max (max 1 2) 3) x = 1 + 2 + 3 + x) : x = -3 := by
  have h0 : max (max (max 1 2) 3) x = max 3 x := by 
    norm_num [max_assoc, max_comm, max_left_comm]
  rw [h0] at h
  by_cases h1 : 3 ≥ x
  · -- Case where 3 ≥ x
    have h2 : max 3 x = 3 := by 
      apply max_eq_left
      linarith
    rw [h2] at h
    linarith
  · -- Case where 3 < x
    have h2 : max 3 x = x := by 
      apply max_eq_right
      linarith
    rw [h2] at h
    linarith