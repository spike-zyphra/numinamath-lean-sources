import Mathlib

theorem algebra_254407 {x y : ℝ} :
    (x + y) * (x^2 + y^2) * (x^4 + y^4) = x^7 + x^6 * y + x^5 * y^2 + x^4 * y^3 + x^3 * y^4 +
    x^2 * y^5 + x * y^6 + y^7 := by 
  ring