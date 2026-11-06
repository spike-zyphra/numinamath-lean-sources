import Mathlib

theorem algebra_232563 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (hxy : x = y + 80) (h : 150 / x = 2 * (150 / y)) :
    (150 / x - 150 / y) = 2 := by
  have h1 : y ≠ 0 := by linarith
  have h2 : x ≠ 0 := by linarith
  field_simp [h1, h2] at h
  nlinarith [hxy, h]