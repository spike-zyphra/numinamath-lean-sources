import Mathlib
open Real

theorem algebra_154213 {f : ℝ → ℝ → ℝ} 
    (h1 : ∀ x y, 0 < x → 0 < y → 0 < f x y ∧ f (x * y) y  = x * f y y) (h2 : ∀ x, 0 < x → 0 < f x 1 ∧ f (f x 1)  x = f x 1)
    (h3 : f 1 1 = 1) : f 19 98 = 19 := by

  have hdiv_98 : f (19 / 98 * 98) 98 = 19 / 98 * f 98 98 := (h1 (19 / 98) 98 (by norm_num) (by norm_num) ).2
  have h98_1: f (98 * 1) 1 = 98 * f 1 1 := (h1 98 1 (by norm_num) (by norm_num) ).2
  have h98_98 : f (f 98 1) 98 = f 98 1 := (h2 98 (by norm_num) ).2

  rw [h3] at h98_1
  simp at h98_1
  rw [h98_1] at h98_98
  rw [h98_98] at hdiv_98
  simp at hdiv_98
  exact hdiv_98

