import Mathlib

theorem algebra_234203 {g : ℝ → ℝ} (h : ∀ x y, g (x - y) = 2022 * (g x + g y) - 2021 * x * y) :
    g 2022 = 2043231 := by 
  have h0 := h 0 0
  have h3 := h 2022 2022
  norm_num at h0 h3
  linarith [h0, h3]