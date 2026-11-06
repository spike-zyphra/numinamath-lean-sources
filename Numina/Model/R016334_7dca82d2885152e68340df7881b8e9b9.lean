import Mathlib

theorem algebra_3675 {a b c : ℝ} (h1 : a * b + b^2 = 326) (h2 : a * b + b * c = 234) (h3 : b^2 + c = 101) :
    8 * a * b + 2 * b^2 + 3 * b * c - 3 * c - 2017 = 12 := by 
  have h4 : c = 101 - b ^ 2 := by linarith [h3]
  have h5 : a * b = 326 - b ^ 2 := by linarith [h1]
  have h7 : b * c = b ^ 2 - 92 := by
    have h8 : a * b + b * c = 234 := by linarith [h2]
    rw [show a * b = 326 - b ^ 2 by linarith [h1]] at h8
    linarith
  have h8 : 8 * a * b + 2 * b ^ 2 + 3 * b * c - 3 * c = 2029 := by
    nlinarith [h4, h5, h7]
  linarith [h8]