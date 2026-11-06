import Mathlib

theorem inequalities_311873 (x y : ℝ) (h : ∀ n : ℕ, 0 < n → n * x + (1 / n) * y ≥ 1) :
    41 * x + 2 * y ≥ 9 := by
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  have h4 := h 4 (by norm_num)
  have h5 := h 5 (by norm_num)
  have h6 := h 6 (by norm_num)
  norm_num at h1 h2 h3 h4 h5 h6 ⊢
  linarith