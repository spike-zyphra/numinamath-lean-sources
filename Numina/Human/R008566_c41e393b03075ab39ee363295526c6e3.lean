import Mathlib

open Polynomial

/- Find the constant coefficient when the polynomial $3(x - 4) + 2(x^2 - x + 7) - 5(x - 1)$ is simplified. -/
theorem algebra_19434 : (3 * (X - 4) + 2 * (X ^ 2 - X + 7) - 5 * (X - 1) : ℤ[X]).coeff 0 = 7 := by norm_num
