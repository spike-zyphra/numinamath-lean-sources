import Mathlib

theorem algebra_178600 {x y z : ℝ}
    (h1 : 2 * x + y + 4 * x * y + 6 * x * z = -6)
    (h2 : y + 2 * z + 2 * x * y + 6 * y * z = 4)
    (h3 : x - z + 2 * x * z - 4 * y * z = -3) :
    x ^ 2 + y ^ 2 + z ^ 2 = 29 := by 
  have eq4 : x + y + z + 3 * x * y + 3 * x * z + 3 * y * z = -1 := by 
    nlinarith
  have eq5 : x + y + z + 2 * x * y + 2 * x * z + 2 * y * z = 1 := by
    nlinarith
  have eq6 : x * y + x * z + y * z = -2 := by
    nlinarith
  have eq7 : x + y + z = 5 := by
    nlinarith [eq6]
  have h : x^2 + y^2 + z^2 = 29 := by 
    have h1 : x + y + z = 5 := eq7
    have h2 : x * y + x * z + y * z = -2 := by linarith [eq6]
    nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  exact h