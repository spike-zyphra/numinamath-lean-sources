import Mathlib

theorem algebra_169590 {a r : ℝ } (hr : r ≠ 0) (ha : a ≠ 0)(h1 : a + a * r = 80) (h2 : a + a * r + a * r^2 + a * r^3 + a * r^4 + a * r^5 = 665) :
    a + a * r + a * r^2 + a * r^3 = 260 := by 
  have eq3 : a + a * r + a * r^2 + a * r^3 + a * r^4 + a * r^5 = (a + a * r) * (1 + r^2 + r^4) := by
    ring_nf
  rw [eq3] at h2 
  rw [h1] at h2
  have h3 : 1 + r^2 + r^4 = 133 / 16 := by
    nlinarith 
  have h4 : r^2 = 9 / 4 := by
    nlinarith [sq_nonneg (r^2 - 9 / 4), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hr]
  have eq6 : a + a * r + a * r^2 + a * r^3 = 80 * (1 + r^2) := by
    have eq5 : a + a * r + a * r^2 + a * r^3 = (a + a * r) * (1 + r^2) := by
      ring_nf
    rw [eq5]
    rw [h1]
    all_goals norm_num 
  rw [eq6]
  nlinarith [h4]