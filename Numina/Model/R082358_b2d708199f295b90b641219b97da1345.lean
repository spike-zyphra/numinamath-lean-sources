import Mathlib

theorem algebra_275014 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h1 : 1 / x = 2) (h2 : 1 / x + 3 / y = 3) :
    x + y = 7 / 2 := by
  have hx' : x = 1 / 2 := by 
    field_simp [hx] at h1
    linarith
  have hy' : y = 3 := by 
    rw [hx'] at h2
    field_simp [hy] at h2
    linarith
  rw [hx', hy']
  norm_num