import Mathlib

theorem algebra_19349 {x : ℝ} (hx : x ≠ 0) (h : x + 1 / x = 7) :
    x^2 + 1 / x^2 + 1 = 48 := by 
  have h2 : x ^ 2 + 1 / x ^ 2 = (x + 1 / x) ^ 2 - 2 := by
    field_simp [hx]
    <;> ring
  rw [h] at h2
  have h1 : x ^ 2 + 1 / x ^ 2 = 47 := by
    rw [h2]
    norm_num
  linarith [h1]