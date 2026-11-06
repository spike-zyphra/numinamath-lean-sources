import Mathlib

theorem algebra_95404 (s b r : ℝ) (_ : s > 0) (_ : b > 0) (_ : r > 0) (hr : r = 5 * s) (hb : b = 2 * r)
    (h : 0.5/s + 30/b + 8/r = 4.25 * 60) : 30/b = 150 := by
  have hb' : b = 10 * s := by
    rw [hb, hr]
    ring
  have hr' : r = 5 * s := by
    linarith
  have eq1 : 0.5 / s + 30 / b + 8 / r = 0.5 / s + 30 / (10 * s) + 8 / (5 * s) := by 
    rw [hb', hr']
  rw [eq1] at h
  have eq2 : 0.5 / s + 30 / (10 * s) + 8 / (5 * s) = (3.5 / s) + (8 / (5 * s)) := by
    field_simp
    ring
  rw [eq2] at h
  have eq3 : (3.5 / s) + (8 / (5 * s)) = (25.5 / (5 * s)) := by
    have h1 : s ≠ 0 := by linarith
    field_simp
    ring
  rw [eq3] at h
  have h4 : 5 * s = 0.1 := by
    have h1 : s ≠ 0 := by linarith
    field_simp at h
    nlinarith
  have h5 : b = 0.2 := by
    rw [hb']
    have h7 : s = 0.02 := by
      nlinarith
    rw [h7]
    norm_num
    <;> nlinarith
  rw [h5]
  norm_num