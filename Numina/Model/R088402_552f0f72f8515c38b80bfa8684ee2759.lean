import Mathlib

theorem algebra_328334 (x y z : ℝ) (h1 : x + y + 2 * z = 6) (h2 : 2 * x * y + y * z + z * x = 4) :
    z ≤ 7 / 3 := by 
  have h3 : x + y = 6 - 2 * z := by linarith 
  have h4 : 2 * x * y = 4 - 6 * z + 2 * z^2 := by 
    have h2' : 2 * x * y + z * (x + y) = 4 := by 
      nlinarith 
    rw [h3] at h2' 
    linarith 
  have h5 : (x + y)^2 ≥ 4 * (x * y) := by 
    nlinarith [sq_nonneg (x - y)]
  have h6 : (x + y)^2 = (6 - 2 * z)^2 := by 
    rw [h3]
  have h7 : 4 * (x * y) = 8 - 12 * z + 4 * z^2 := by
    have h8 : x * y = 2 - 3 * z + z^2 := by 
      nlinarith [h4]
    linarith [h8]
  rw [h6] at h5
  rw [h7] at h5 
  nlinarith