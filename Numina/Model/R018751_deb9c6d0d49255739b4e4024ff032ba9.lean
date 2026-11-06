import Mathlib

theorem inequalities_171306 (x y : ℝ) (h : ∀ n : ℕ, 0 < n → n * x + (1 / n) * y ≥ 1) :
    41 * x + 2 * y ≥ 9 := by 
  have h1 := h 1 (by norm_num)
  norm_num at h1
  have h2 := h 2 (by norm_num)
  norm_num at h2
  have h3 := h 3 (by norm_num)
  norm_num at h3
  have h4 := h 4 (by norm_num)
  norm_num at h4
  have h5 := h 5 (by norm_num)
  norm_num at h5
  have h41 := h 41 (by norm_num)
  norm_num at h41
  have h6 := h 82 (by norm_num)
  norm_num at h6
  linarith