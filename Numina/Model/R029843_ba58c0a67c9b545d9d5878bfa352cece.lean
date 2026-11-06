import Mathlib

theorem algebra_22475 {a b : ℝ} (l₁ : ℝ → ℝ) (h : ∀ x, l₁ x = a * (x + 3) + b - 2)
    (ha' : l₁ 5 = 8) (hb' : l₁ 7 = 14) : a - b = 17 := by
  have eq1 : l₁ 5 = a * (5 + 3) + b - 2 := h 5
  have eq2 : l₁ 7 = a * (7 + 3) + b - 2 := h 7
  rw [eq1] at ha'
  rw [eq2] at hb'
  norm_num at ha' hb'
  have h1 : a = 3 := by
    linarith
  have h2 : b = -14 := by
    linarith [ha', h1]
  linarith [h1, h2]