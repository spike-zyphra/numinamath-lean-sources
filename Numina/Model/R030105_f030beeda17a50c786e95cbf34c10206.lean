import Mathlib

theorem algebra_281051 {x y : ℝ} (h₀ : x / y = 2 / 5) (h₁ : (x + 9) / (y + 9) = 3 / 7) :
    (x + 18) / (y + 18) = 5 / 11 := by
  have h2 : y ≠ 0 := by
    by_contra h
    have hy : y = 0 := by linarith
    rw [hy] at h₀
    norm_num at h₀
  have h3 : y + 9 ≠ 0 := by
    by_contra h
    have hy9 : y + 9 = 0 := by linarith
    rw [show y + 9 = 0 from hy9] at h₁
    norm_num [h2] at h₁
  have h4 : 5 * x = 2 * y := by
    have hne : y ≠ 0 := h2
    field_simp at h₀
    linarith
  have h5 : 7 * (x + 9) = 3 * (y + 9) := by
    have hne9 : y + 9 ≠ 0 := h3
    field_simp at h₁
    linarith
  have h6 : y = 180 := by
    nlinarith [h4, h5]
  have h7 : x = 72 := by
    rw [h6] at h4
    linarith
  have h8 : y + 18 ≠ 0 := by
    rw [h6]
    norm_num
  -- Calculate the final ratio to be 5/11
  field_simp at *
  rw [show x + 18 = (90 : ℝ) by linarith, show y + 18 = (198 : ℝ) by linarith]
  all_goals
    norm_num