import Mathlib

theorem algebra_146660 (x : ℝ) (hx : x > 0) (h : 15000 / x = 25000 / (x - 15000)) :
    x = 9375 := by
  have hx1 : x - 15000 ≠ 0 := by
    by_contra h1
    have h2 : x = 15000 := by linarith
    rw [h2] at h
    norm_num [h2] at h
  have hx2 : x ≠ 0 := by linarith
  have h1 : 15000 * (x - 15000) = 25000 * x := by 
    field_simp [show x ≠ 0 by linarith, show x - 15000 ≠ 0 by assumption] at h ⊢
    nlinarith
  nlinarith [sq_pos_of_pos (show 0 < x by linarith)]