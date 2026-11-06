import Mathlib

theorem algebra_234016 {g : ℝ → ℝ} (h : ∀ x y, g (x - y) = g x + g y - 2021 * (x + y)) :
    g 2022 = 4086462 := by 
  have h1 := h 0 0
  have h2 := h (2022 : ℝ) 0
  have h3 := h 0 (2022 : ℝ)
  norm_num at h1 h2 h3
  linarith