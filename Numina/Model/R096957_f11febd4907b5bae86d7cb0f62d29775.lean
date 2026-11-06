import Mathlib

theorem algebra_269854 {x : ℝ} (hx : x ≠ 0) (h : 1 / (3 / 10) = 1 / x + 1) :
    x = 3 / 7 := by
  have h1 : 1 / (3 / 10 : ℝ) = 10 / 3 := by
    norm_num
  rw [h1] at h
  have h2 : 1 / x = 7 / 3 := by 
    linarith
  field_simp [hx] at h2 ⊢
  linarith