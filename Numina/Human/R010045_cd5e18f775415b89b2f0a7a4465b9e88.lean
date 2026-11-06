import Mathlib

/- The vertex of the parabola described by the equation $y=-3x^2-30x-81$ is $(m,n)$. What is $n$? -/
theorem algebra_13280 (a m n : ℝ) (ha : a ≠ 0) (h : ∀ x, -3 * x ^ 2 - 30 * x - 81 = a * (x - m) ^ 2 + n) :
    n = -6 := by
  nlinarith [h 0, h 1, h 2]
