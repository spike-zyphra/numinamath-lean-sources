import Mathlib


theorem algebra_596874 {f : ℝ → ℝ} (h₀ : ∀ x > 0, deriv f x < 0)
    (h₁ : ∀ x y, f (x * y) = f x + f y) (h₂ : f (1 / 3) = 1) :
    f 1 = 0 ∧ ∀ x, f x + f (2 - x) < 2 ↔ 0 < x ∧ x < 1 + Real.sqrt 10 / 3 := by

  have h3 : f 0 = 0 := by
    have h4 : f (0 * 0) = f 0 + f 0 := h₁ 0 0
    norm_num at h4
    linarith

  have h4 : f (0 * (1/3 : ℝ)) = f 0 + f (1/3 : ℝ) := h₁ 0 (1/3 : ℝ)
  have h5 : f (0 * (1/3 : ℝ)) = f 0 := by
    norm_num
  have h6 : f (1/3 : ℝ) = 0 := by
    linarith [h4, h5, h3]

  have h7 : f (1/3 : ℝ) = 1 := h₂
  linarith [h6, h7]