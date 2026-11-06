import Mathlib

theorem algebra_297975 {f : ℝ → ℝ} (h : ∀ x y, f x + f (2 * x + y) = f (3 * x - y) + x - 2010) :
    f 2010 = 0 := by
  have eq1 : ∀ x : ℝ, f x = x - 2010 := by
    intro x
    have h1 := h x (x / 2)
    have eq2 : 2 * x + (x / 2 : ℝ) = (5 * x / 2 : ℝ) := by ring
    have eq3 : 3 * x - (x / 2 : ℝ) = (5 * x / 2 : ℝ) := by ring
    rw [eq2, eq3] at h1 
    linarith
  have eq1_2010 := eq1 2010
  norm_num at eq1_2010 ⊢
  linarith