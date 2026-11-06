import Mathlib

theorem algebra_2889 (a b c : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 2 + b * x + c)
    (h2 : f 2 = 15) (h3 : f (-2) = -5) (h4 : f (-1) = -9) :
    a + b + c = 1 := by
  have eq1 := hf 2
  rw [eq1] at h2
  have eq2 := hf (-2)
  rw [eq2] at h3
  have eq3 := hf (-1)
  rw [eq3] at h4
  linarith