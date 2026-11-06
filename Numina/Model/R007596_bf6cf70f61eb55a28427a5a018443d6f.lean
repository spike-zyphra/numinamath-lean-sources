import Mathlib

theorem algebra_9465 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 5 + b * x ^ 3 + 2)
    (h : f 2 = 7) : f (-2) = -3 := by
  have eq1 : f 2 = a * 2^5 + b * 2^3 + 2 := hf 2
  rw [eq1] at h
  have eq2 : f (-2) = a * (-2) ^ 5 + b * (-2) ^ 3 + 2 := hf (-2)
  rw [eq2]
  linarith