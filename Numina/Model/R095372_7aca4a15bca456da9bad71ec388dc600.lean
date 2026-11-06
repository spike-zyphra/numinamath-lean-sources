import Mathlib

theorem algebra_194168 {x y : ℝ} (h₀ : x + y = 40) (h₁ : x * y = 20) :
    1 / x + 1 / y = 2 := by
  have hx : x ≠ 0 := by
    by_contra h
    rw [h] at h₁
    nlinarith
  have hy : y ≠ 0 := by
    by_contra h
    rw [h] at h₁
    nlinarith
  have h2 : 1 / x + 1 / y = (x + y) / (x * y) := by
    field_simp [hx, hy]
    <;> ring
  rw [h2]
  rw [h₀, h₁]
  all_goals norm_num
  all_goals linarith