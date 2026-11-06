import Mathlib

theorem algebra_167544 (a : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 4 - 8 * x ^ 3 + 14 * x ^ 2 + a * x)
    (h : ∀ x, ∃ y, f x = y ∧ f (-x) = -y) : a = 8 := by
  have h1 := h 1
  rcases h1 with ⟨y1, hy1, hn1⟩
  have h2 := h (-1)
  rcases h2 with ⟨y2, hy2, hn2⟩
  have eq1 := hf 1
  have eq2 := hf (-1)
  linarith