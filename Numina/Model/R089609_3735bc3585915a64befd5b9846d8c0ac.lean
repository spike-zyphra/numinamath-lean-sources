import Mathlib

theorem algebra_19175 {x y : ℝ} (h : x / y = 1 / 2) (h' : y = 4 * x - 36) :
    x = 18 := by
  have h₀ : y ≠ 0 := by
    by_contra h₀
    rw [h₀] at h
    norm_num at h
  have h₁ : 2 * x = y := by
    field_simp [h₀] at h
    linarith
  rw [show y = 4 * x - 36 by linarith [h']] at h₁
  linarith