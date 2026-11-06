import Mathlib

theorem algebra_603 (v w : ℝ) (hw : w > 0) (h1 : 90 / (v + w) = 10) (h2 : 70 / (v - w) = 10) :
    100 / v = 12.5 := by
  have h1' : v + w ≠ 0 := by
    by_contra h
    have : v + w = 0 := by linarith
    rw [this] at h1
    norm_num at h1
    all_goals try linarith
  have h2' : v - w ≠ 0 := by
    by_contra h
    have : v - w = 0 := by linarith
    rw [this] at h2
    norm_num at h2
    all_goals try linarith

  have eq1 : 90 = 10 * (v + w) := by
    have h : v + w ≠ 0 := h1'
    field_simp [h] at h1
    linarith

  have eq2 : 70 = 10 * (v - w) := by
    have h : v - w ≠ 0 := h2'
    field_simp [h] at h2
    linarith

  have h3 : v + w = 9 := by
    linarith

  have h4 : v - w = 7 := by
    linarith

  have h5 : v = 8 := by
    linarith [h3, h4]

  rw [h5]
  norm_num