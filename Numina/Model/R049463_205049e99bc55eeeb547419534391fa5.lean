import Mathlib

theorem algebra_593 (x : ℝ) (h : 6 / 5 + 3 / (2 * x) = 7 / 15) (hx : 2 * x ≠ 0) :
    x = -45 / 22 := by
  have h1 : 3 / (2 * x) = 7 / 15 - 6 / 5 := by 
    field_simp [hx] at h ⊢
    linarith
  have h2 : 3 / (2 * x) = -11 / 15 := by 
    rw [h1]
    norm_num
  field_simp [hx] at h2
  linarith