import Mathlib

theorem algebra_230284 {x : ℝ} (hx : x ≠ 0) (h : (1 - 80 / 100) * x = (1 - 20 / 100) * (x * (1 - y / 100))) :
    y = 75 := by
  have h1 : (1 - 80 / 100 : ℝ) * x = (1 - 20 / 100 : ℝ) * (x * (1 - y / 100)) := by
    linarith
  have eq1 : (1 - 80 / 100 : ℝ) = (1 / 5 : ℝ) := by
    norm_num
  have eq2 : (1 - 20 / 100 : ℝ) = (4 / 5 : ℝ) := by
    norm_num
  rw [eq1] at h1
  rw [eq2] at h1
  have eq3 : (1 / 5) * x = (4 / 5) * (x * (1 - y / 100)) := by
    linarith [h1]
  have h2 : (x) ≠ 0 := hx
  have h3 : 1 / 5 = 4 / 5 * (1 - y / 100) := by
    apply (mul_left_inj' h2).mp
    linarith [eq3]
  have h4 : 1 - y / 100 = (1 / 4 : ℝ) := by
    linarith [h3]
  linarith [h4]