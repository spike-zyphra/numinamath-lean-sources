import Mathlib

theorem algebra_300580 {a b : ℝ} (h : a ≠ 0) (h' : b ≠ 0)
    (h'' : ∀ x : ℝ, 2 * (a - b) * x ^ 2 + (2 * b - a * b) * x + (a * b - 2 * a) = 0 → x = -1) :
    2 / b - 1 / a = 1 / 2 := by

  have h1 := h'' 1 (by 
    ring
  )

  have h2 : (1 : ℝ) = -1 := by
    linarith

  have h3 : (1 : ℝ) + (1 : ℝ) = (0 : ℝ) := by
    linarith [h2]

  have h4 : (1 : ℝ) + (1 : ℝ) ≠ (0 : ℝ) := by
    norm_num

  contradiction