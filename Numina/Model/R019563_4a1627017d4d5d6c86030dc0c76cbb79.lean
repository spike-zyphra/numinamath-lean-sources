import Mathlib

theorem algebra_120985 (x : ℝ) (h : max (max 1 x) (max 2 3) = 1 + 2 + 3 + x) :
    x = -3 := by
  have h1 : max (max 1 x) (max 2 3) = max (max 1 x) 3 := by
    norm_num
  rw [h1] at h
  by_cases h2 : max (1 : ℝ) x ≥ (3 : ℝ)
  · -- case 1: max 1 x ≥ 3
    have h3 : max (max 1 x) 3 = max 1 x := by
      rw [max_eq_left]
      linarith
    rw [h3] at h
    by_cases h4 : x ≥ (1 : ℝ)
    · -- x ≥ 1
      have h5 : max (1 : ℝ) x = x := by
        apply max_eq_right
        linarith
      rw [h5] at h
      linarith
    · -- x < 1
      have h6 : max (1 : ℝ) x = (1 : ℝ) := by
        apply max_eq_left
        linarith
      rw [h6] at h
      linarith
  · -- case 2: max 1 x < 3
    have h3 : max (max 1 x) 3 = (3 : ℝ) := by
      rw [max_eq_right]
      linarith
    rw [h3] at h
    linarith