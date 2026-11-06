import Mathlib

theorem algebra_234232 {g : ℝ → ℝ} (h : ∀ x y, g (x - y) = 2021 * g x + 2021 * g y - 2022 * x * y) :
    g 2021 = 2043231 := by 
  have h1 := h 0 0
  simp at h1
  have h0 : g 0 = 0 := by linarith
  have h2 := h (2021) 0
  simp [h0] at h2
  have h3 := h 0 (2021)
  simp [h0] at h3
  have h4 := h 2021 2021
  simp [h0] at h4
  linarith