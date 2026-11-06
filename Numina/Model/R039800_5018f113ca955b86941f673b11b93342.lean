import Mathlib

theorem algebra_10164 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = 2 * f x + 2 * f y + 3 * x * y)
    (h' : 2 * f 1 * f (-1) ≥ 9 / 8) : f (3 / 4) = 9 / 32 := by

  -- Let's compute f(0) by setting x = 0 and y = 0
  have h1 : f 0 = 0 := by
    have h00 := h 0 0
    norm_num at h00
    linarith

  -- Show that f(x) = 0 for all x
  have h2 : ∀ x, f x = 0 := by
    intro x
    have hx0 := h x 0
    simp [h1] at hx0
    nlinarith

  -- Therefore f(1) = 0 and f(-1) = 0
  have h3 : f 1 = 0 := h2 1
  have h4 : f (-1) = 0 := h2 (-1)

  -- Compute 2 * f 1 * f (-1)
  have h5 : 2 * f 1 * f (-1) < 9 / 8 := by
    rw [h3, h4]
    norm_num

  -- Contradicts with h'
  linarith