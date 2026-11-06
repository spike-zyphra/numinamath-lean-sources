import Mathlib

theorem algebra_124009 (x : ℝ) (h : max (max 1 x) (max 2 3) - min (min 1 x) (min 2 3) = 1 + 2 + 3 + x) :
    x = -3 / 2 := by
  have h1 : max (max 1 x) (max 2 3) = max (max 1 x) 3 := by
    norm_num
  have h2 : min (min 1 x) (min 2 3) = min (min 1 x) 2 := by
    norm_num
  rw [h1, h2] at h
  by_cases h3 : x ≤ 1
  · -- Case 1 : x ≤ 1
    have hx1 : min (min 1 x) 2 = x := by
      have hx1 : min (1 : ℝ) x = x := by
        apply min_eq_right
        linarith
      rw [hx1]
      apply min_eq_left
      linarith
    have hx2 : max (max (1 : ℝ) x) 3 = 3 := by
      have hx2 : max (1 : ℝ) x = 1 := by
        apply max_eq_left
        linarith
      rw [hx2]
      norm_num
    rw [hx1, hx2] at h
    linarith
  · -- Case 2 : x > 1
    by_cases h4 : x ≤ 3
    · -- Case 2a : x ≤ 3
      have hx1 : min (min (1 : ℝ) x) 2 = 1 := by
        have hx1 : min (1 : ℝ) x = 1 := by
          apply min_eq_left
          linarith
        rw [hx1]
        norm_num
      have hx2 : max (max (1 : ℝ) x) 3 = 3 := by
        have hx2 : max (1 : ℝ) x = x := by
          apply max_eq_right
          linarith
        rw [hx2]
        apply max_eq_right
        linarith
      rw [hx1, hx2] at h
      linarith
    · -- Case 2b : x > 3
      have hx1 : min (min (1 : ℝ) x) 2 = 1 := by
        have hx1 : min (1 : ℝ) x = 1 := by
          apply min_eq_left
          linarith
        rw [hx1]
        norm_num
      have hx2 : max (max (1 : ℝ) x) 3 = x := by
        have hx2 : max (1 : ℝ) x = x := by
          apply max_eq_right
          linarith
        rw [hx2]
        apply max_eq_left
        linarith
      rw [hx1, hx2] at h
      linarith