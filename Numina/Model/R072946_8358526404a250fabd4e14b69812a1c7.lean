import Mathlib

theorem algebra_14458 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (h₀ : x^2 + y^2 = 193) (h₁ : x * y = 84) :
    x + y = 19 := by
  have h2 : (x + y) ^ 2 = 361 := by
    nlinarith [h₀, h₁]
  have h3 : x + y = 19 := by
    nlinarith
  exact h3