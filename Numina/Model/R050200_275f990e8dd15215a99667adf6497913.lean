import Mathlib

theorem algebra_310513 (f : ℝ → ℝ) (h : ∀ x y, f (x + y) = f x + f y + 2 * (x + y) + 1)
    (h1 : f 1 = 1) (a : ℝ) (ha : ∀ x : ℕ, x > 0 → x ≥ 2 → f x ≥ (a + 7) * x - (a + 10)) :
    a ≤ 2 := by
  have h2 := h 0 0
  simp at h2
  have h3 : f 0 = -1 := by linarith
  have h4 := h 1 0
  norm_num [h1, h3] at h4
  all_goals nlinarith