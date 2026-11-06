import Mathlib

/- Positive real numbers $x,y$ satisfy the equations $x^2 + y^2 = 1$ and $x^4 + y^4= \frac{17}{18}$.  Find $xy$. -/
theorem algebra_20921 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : x^2 + y^2 = 1) (h2 : x^4 + y^4 = 17 / 18) : x * y = 1 / 6 := by 
  have h3 : 0 < x * y := mul_pos hx hy
  nlinarith [sq_nonneg (x - y)]