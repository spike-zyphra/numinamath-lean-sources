import Mathlib

theorem inequalities_80694 (r s u v : ℝ) :
    min (min (min (r - s^2) (s - u^2)) (u - v^2)) (v - r^2) ≤ 1 / 4 := by 
  by_contra h
  have h1 : min (min (min (r - s^2) (s - u^2)) (u - v^2)) (v - r^2) > 1 / 4 := by 
    linarith
  have h2 : r - s^2 > 1 / 4 := by 
    by_contra h2
    push_neg at h2
    have h3 : min (min (min (r - s^2) (s - u^2)) (u - v^2)) (v - r^2) ≤ r - s^2 := by 
      simp [min_le_iff]
    linarith [h1, h3, h2]
  have h3 : s - u^2 > 1 / 4 := by 
    by_contra h3
    push_neg at h3
    have h4 : min (min (min (r - s^2) (s - u^2)) (u - v^2)) (v - r^2) ≤ s - u^2 := by 
      simp [min_le_iff]
    linarith [h1, h4, h3]
  have h4 : u - v^2 > 1 / 4 := by 
    by_contra h4
    push_neg at h4
    have h5 : min (min (min (r - s^2) (s - u^2)) (u - v^2)) (v - r^2) ≤ u - v^2 := by 
      simp [min_le_iff]
    linarith [h1, h5, h4]
  have h5 : v - r^2 > 1 / 4 := by 
    by_contra h5
    push_neg at h5
    have h6 : min (min (min (r - s^2) (s - u^2)) (u - v^2)) (v - r^2) ≤ v - r^2 := by 
      simp [min_le_iff]
    linarith [h1, h6, h5]
  nlinarith [sq_nonneg (r - 1 / 2), sq_nonneg (s - 1 / 2), sq_nonneg (u - 1 / 2), sq_nonneg (v - 1 / 2)]