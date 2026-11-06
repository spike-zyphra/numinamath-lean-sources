import Mathlib

/- A large rectangle has side lengths of $(x+7)$ and $(x+5)$. In the large rectangle, there is a rectangular hole with side lengths of $(2x-3)$ and $(x-2)$. What is the area of the large rectangle (not including the area of the hole)? Express your answer as a polynomial in $x$. -/
theorem algebra_15253 {x : ℝ} (hx : x > 0) :
    (x + 7) * (x + 5) - (2 * x - 3) * (x - 2) = -x ^ 2 + 19 * x + 29 := by 
  nlinarith [hx]