import Mathlib

theorem algebra_149635 (a : ℕ → ℝ) (h₀ : Monotone a)
    (h₁ : a 1 = 1) (h₂ : ∀ n, 0 < a n)
    (h₃ : ∏' k, a (2 * k - 1) = ∏' k, a (2 * k))
    (h₄ : ∀ k, a (2 * k) = a (2 * k - 2) - a (2 * k - 1)) :
    ∑' k, a k = 4 := by
  have h5 := h₄ 0
  norm_num at h5
  have h6 : a 0 = 0 := by linarith [h5]
  have h7 : 0 < a 0 := h₂ 0
  linarith [h6, h7]