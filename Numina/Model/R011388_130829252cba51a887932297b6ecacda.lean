import Mathlib

theorem algebra_24908 {x y z : ℝ} (h1 : x + y + z = 3) (h3 : x^3 + y^3 + z^3 = 15) (h4 : x^4 + y^4 + z^4 = 35) (h2u : x^2 + y^2 + z^2 < 10) :
  x^5 + y^5 + z^5 = 83 := by
  have eq1 : x * y + y * z + z * x = ((x+y+z)^2 - (x^2+y^2+z^2))/2 := by ring
  have eq2 : x^3 + y^3 + z^3 = (x+y+z) ^3 - 3 * (x+y+z) * (x * y + y * z + z * x) + 3 * (x*y*z) := by ring
  have eq3 : x^4 + y^4 + z^4 = (x^2+y^2+z^2)^2 - 2 * ((x * y + y * z + z * x)^2 - 2 * (x*y*z) * (x+y+z)) := by ring
  have h5 : x^2 + y^2 + z^2 = 7 := by
    have eq6 : x^4 + y^4 + z^4 = (x^2+y^2+z^2) ^2 - 2 * ((x * y + y * z + z * x) ^2 - 2 * (x * y * z) * (x+y+z)) := by
      ring
    rw [h4, h1] at eq6
    have eq7 : x^3 + y^3 + z^3 = (x+y+z) ^3 - 3 * (x+y+z) * (x * y + y * z + z * x) + 3 * (x*y*z) := by
      ring
    rw [h3, h1] at eq7
    have eq8 : x^2 + y^2 + z^2 = (x+y+z) ^2 - 2 * (x * y + y * z + z * x) := by
      ring
    rw [h1] at eq8
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x + y + z - 3), sq_nonneg (x^2 + y^2 + z^2 - 7)]
  have h7 : x * y + y * z + z * x = 1 := by
    have eq4 : x^2 + y^2 + z^2 = (x+y+z) ^2 - 2 * (x * y + y * z + z * x) := by
      ring
    rw [h5, h1] at eq4
    linarith
  have h8 : x * y * z = -1 := by
    have eq4 : x^3 + y^3 + z^3 = (x+y+z) ^3 - 3 * (x+y+z) * (x * y + y * z + z * x) + 3 * (x*y*z) := by
      ring
    rw [h3, h1, h7] at eq4
    linarith
  have eq5 : x^5 + y^5 + z^5 = (x + y + z) * (x^4 + y^4 + z^4) - (x*y+y*z+z*x) * (x^3+y^3+z^3) + (x*y*z) * (x^2+y^2+z^2) := by ring
  rw [eq5]
  rw [h1, h4, h7, h3, h8, h5]
  norm_num