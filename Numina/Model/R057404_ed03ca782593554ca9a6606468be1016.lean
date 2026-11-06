import Mathlib

theorem algebra_203352 {x y : ℝ} (h₀ : x + y = 17) (h₁ : x * y = 17) :
    (x ^ 2 - 17 * x) * (y + 17 / y) = -289 := by
  have h2 : y ≠ 0 := by
    by_contra h
    have h3 : x * y = 0 := by
      rw [h]
      norm_num
    linarith [h₁, h3]
  have h3 : x ≠ 0 := by
    by_contra h
    have h4 : x * y = 0 := by
      rw [h]
      norm_num
    linarith [h₁, h4]
  have h4 : y + 17 / y = 17 := by
    have h5 : y ≠ 0 := h2
    have h6 : y + 17 / y = x + y := by
      field_simp [h5]
      nlinarith [h₁]
    linarith [h6, h₀]
  have h7 : x^2 - 17 * x = -17 := by
    nlinarith [sq_nonneg (x - 17/2), sq_nonneg (y - 17/2), h₀, h₁]
  rw [h7] at *
  rw [h4] at *
  nlinarith