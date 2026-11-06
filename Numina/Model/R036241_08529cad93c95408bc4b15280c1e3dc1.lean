import Mathlib

theorem algebra_97483 (x v : ℝ) (h : x > 0) (h1 : v > 0) (h1': v-(20/60) > 0)
(h2 : 180 = x/v)
(h3 : 276 = (x/3)/v + (2*x/3)/(v-(20/60))) :
  x = 135 := by
  have h4 : v = x / 180 := by
    field_simp [(show v ≠ 0 by linarith)] at h2 ⊢
    linarith
  have h5 : 276 = (x / 3) / (x / 180) + (2 * x / 3) / ((x / 180) - (20 / 60)) := by
    rw [h4] at h3
    simpa using h3
  have h6 : (x / 3) / (x / 180) = 60 := by
    have hx1 : x ≠ 0 := by linarith
    field_simp at *
    <;> ring_nf
    <;> norm_num
    <;> nlinarith
  have hx2 : x - 60 ≠ 0 := by
    by_contra h8
    have h8' : x = 60 := by linarith
    rw [h4] at h1'
    rw [h8'] at h1'
    norm_num at h1'
    all_goals linarith
  have h7 : (2 * x / 3) / ((x / 180) - (20 / 60)) = (120 * x) / (x - 60) := by
    have hx3 : (x / 180) - (20 / 60) = (x - 60) / 180 := by
      linarith
    rw [hx3]
    have hx4 : x - 60 ≠ 0 := hx2
    field_simp [hx4]
    <;> ring_nf
    <;> norm_num
    <;> nlinarith
  rw [h6, h7] at h5
  have h8 : (120 * x) / (x - 60) = 216 := by
    linarith
  have hx3 : 120 * x = 216 * (x - 60) := by
    have hx2' : x - 60 ≠ 0 := hx2
    have eq3 : (120 * x) / (x - 60) = 216 := h8
    have : 120 * x = 216 * (x - 60) := by
      field_simp [hx2'] at eq3 ⊢
      linarith
    linarith
  linarith