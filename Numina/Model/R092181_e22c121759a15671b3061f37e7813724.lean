import Mathlib

theorem algebra_318211 {a b c : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 5 + b * x ^ 3 + c * x + 10)
    (h : f 3 = 3) : f (-3) = 17 := by
  have eq1 : f 3 = a * 3 ^ 5 + b * 3 ^ 3 + c * 3 + 10 := hf 3
  rw [eq1] at h -- get the equation from f(3) = 3
  -- express $f(-3)$
  have eq2 : f (-3) = a * (-3) ^ 5 + b * (-3) ^ 3 + c * (-3) + 10 := hf (-3)
  rw [eq2]
  -- simplification
  have h1 : a * (-3) ^ 5 + b * (-3) ^ 3 + c * (-3) = - (a * 3 ^ 5 + b * 3 ^ 3 + c * 3) := by
    ring
  -- now compute the value
  linarith [h1, h]