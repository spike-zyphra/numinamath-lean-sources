import Mathlib

theorem algebra_285903 {x y z : ℝ} (h1 : x + y + z = 1) (h2 : x^2 + y^2 + z^2 = 2) (h3 : x^3 + y^3 + z^3 = 3) :
    x^4 + y^4 + z^4 = 25 / 6 := by 

  have h4 : x * y + y * z + z * x = -1 / 2 := by 
    have h5 : x^2 + y^2 + z^2 = (x + y + z) ^ 2 - 2 * (x * y + y * z + z * x) := by ring
    rw [h1] at h5
    linarith

  have h5 : x * y * z = 1 / 6 := by
    have eq6 : x^3 + y^3 + z^3 = (x + y + z) ^ 3 - 3 * (x + y + z) * (x * y + y * z + z * x) + 3 * (x * y * z) := by ring
    rw [h1, h4] at eq6
    linarith

  have h6 : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 = -1 / 12 := by
    have h7 : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 = (x * y + y * z + z * x) ^ 2 - 2 * (x * y * z) * (x + y + z) := by 
      ring
    rw [h7, h4, h5, h1]
    norm_num

  have h7 : x^4 + y^4 + z^4 = (x^2 + y^2 + z^2) ^ 2 - 2 * (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) := by ring
  rw [h7, h2, h6]
  norm_num