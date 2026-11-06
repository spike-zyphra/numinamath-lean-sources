import Mathlib

theorem algebra_61504 {x y z : ℝ} (h1 : x^2 + 4*y^2 + 16*z^2 = 48) (h2 : x*y + 4*y*z + 2*z*x = 24) :
    x^2 + y^2 + z^2 = 21 := by
  nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (y - 2 * z), sq_nonneg (x - 4 * z)]