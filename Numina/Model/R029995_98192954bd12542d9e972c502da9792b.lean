import Mathlib

theorem algebra_225686 {f : ℝ → ℝ}
    (h₁ : f 1 = 1)
    (h₂ : ∀ x, 0 < x → f x > 0)
    (h₃ : ∀ x y, f (x + y) - f (x - y) = 2 * f (1 - x) * f y) :
    f (1 / 3) = 1 / 2 := by

  have h0 : f 0 = 0 := by
    have h4 := h₃ 1 0
    norm_num [h₁] at h4
    nlinarith

  have h4 := h₃ (2 / 3) (1 / 3)
  have h5 : f (2 / 3 + 1 / 3) - f (2 / 3 - 1 / 3) = 2 * f (1 - (2 / 3)) * f (1 / 3) := by
    apply h₃
  have h6 : f (2 / 3 + 1 / 3) = f 1 := by
    norm_num
  have h7 : f (2 / 3 - 1 / 3) = f (1 / 3) := by
    norm_num
  have h8 : f (1 - (2 / 3)) = f (1 / 3) := by
    norm_num
  rw [h6, h7, h8] at h5
  rw [h₁] at h5
  have h8 : f (1 / 3) > 0 := by
    apply h₂
    norm_num
  nlinarith [sq_nonneg (f (1 / 3) - 1 / 2), sq_nonneg (f (1 / 3) + 1), h8]