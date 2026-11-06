import Mathlib

theorem algebra_209329 {x y t : ℝ} (h₀ : x + y = t) (h₁ : x^2 + y^2 = t)
    (h₂ : x^3 + y^3 = t) : x^4 + y^4 = t := by
  nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]