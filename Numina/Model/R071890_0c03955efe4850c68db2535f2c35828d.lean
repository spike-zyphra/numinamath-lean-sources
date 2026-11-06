import Mathlib

theorem algebra_72613 {x y z : ℝ} (h₀ : x + y + z = 13) (h₁ : x * y * z = 72)
    (h₂ : 1 / x + 1 / y + 1 / z = 3 / 4) :
    x ^ 2 + y ^ 2 + z ^ 2 = 61 := by
  have h3 : x ≠ 0 := by
    by_contra h
    rw [h] at h₁
    nlinarith
  have h4 : y ≠ 0 := by
    by_contra h
    rw [h] at h₁
    nlinarith
  have h5 : z ≠ 0 := by
    by_contra h
    rw [h] at h₁
    nlinarith
  have h₃ : x * y + x * z + y * z = 54 := by
    have h₂' : x * y * z ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact h3
      exact h4
      exact h5
    field_simp [h3, h4, h5] at h₂
    nlinarith [h₁]
  have h₄ : x ^ 2 + y ^ 2 + z ^ 2 = (x + y + z) ^ 2 - 2 * (x * y + x * z + y * z) := by
    ring
  rw [h₄, h₀, h₃]
  norm_num