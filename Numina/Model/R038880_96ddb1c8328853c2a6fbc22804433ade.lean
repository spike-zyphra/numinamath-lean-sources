import Mathlib

theorem algebra_176187 {x y z : ℝ} (h₀ : x * y = 6) (h₁ : x - z = 2) (h₂ : x + y + z = 9) :
    x / y - z / x - z ^ 2 / (x * y) = 2 := by

  have hz : z = x - 2 := by
    linarith

  have h₃ : 2 * x + y = 11 := by
    have h₃ : z = x - 2 := hz
    rw [h₃] at h₂
    linarith

  have h₄ : x ≠ 0 := by
    by_contra h
    have h₅ : x * y = 0 := by
      rw [h]
      norm_num
    linarith

  have h₅ : y ≠ 0 := by
    by_contra h
    have h₆ : x * y = 0 := by
      rw [h]
      norm_num
    linarith

  have eq1 : x / y - z / x - z ^ 2 / (x * y) = (x^2 - z * y - z^2) / (x * y) := by
    field_simp [h₄, h₅]
    <;> ring

  rw [eq1]
  rw [hz]
  have h₆ : x^2 - (x - 2) * y - (x - 2)^2 = 12 := by
    nlinarith [h₀, h₃]

  rw [h₆]
  rw [h₀]
  all_goals norm_num