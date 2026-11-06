import Mathlib

theorem algebra_4816 (v : ℝ) (h : v > 0) (h1 : 90 / (v + w) = 6) (h2 : 90 / (v - w) = 10) (h3 : 90 / (b + w) = 5) :
    90 / (b - w) = 15 / 2 := by

  have eq1 : v + w = 15 := by
    have h1' : 90 / (v + w) = 6 := h1
    have hne1 : v + w ≠ 0 := by
      by_contra h0
      rw [h0] at h1'
      norm_num at h1'
    field_simp [hne1] at h1'
    linarith

  have eq2 : v - w = 9 := by
    have h2' : 90 / (v - w) = 10 := h2
    have hne2 : v - w ≠ 0 := by
      by_contra h0
      rw [h0] at h2'
      norm_num at h2'
    field_simp [hne2] at h2'
    linarith

  have eq3 : v = 12 := by
    linarith [eq1, eq2]

  have eq4 : w = 3 := by
    linarith [eq1, eq3]

  have eq5 : b + w = 18 := by
    have h3' : 90 / (b + w) = 5 := h3
    have hne3 : b + w ≠ 0 := by
      by_contra h0
      rw [h0] at h3'
      norm_num at h3'
    field_simp [hne3] at h3'
    linarith

  have eq6 : b = 15 := by
    linarith [eq5, eq4]

  have eq7 : b - w = 12 := by
    linarith [eq6, eq4]

  have eq8 : (90 / (b - w) : ℝ) = (15 / 2 : ℝ) := by
    have h8 : (b - w : ℝ) = (12 : ℝ) := eq7
    rw [h8]
    norm_num
  linarith [eq8]