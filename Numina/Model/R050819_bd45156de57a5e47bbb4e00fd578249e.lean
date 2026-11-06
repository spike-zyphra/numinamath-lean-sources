import Mathlib

theorem algebra_287833 (x y z : ℝ) (h₀ : x + y + z = 9) (h₁ : x * y + y * z + z * x = 24) :
    z ≤ 5 := by 
  have h2 : x + y = 9 - z := by linarith
  have h3 : x * y = z^2 - 9 * z + 24 := by
    have h2' : x + y = 9 - z := by linarith
    have : x * y + z * (x + y) = 24 := by linarith
    rw [h2'] at this
    nlinarith 
  have h4 : (x - y) ^ 2 ≥ 0 := by 
    apply sq_nonneg 
  have h5 : (x + y) ^ 2 - 4 * (x * y) ≥ 0 := by 
    nlinarith [h4, sq_nonneg (x + y), sq_nonneg (x - y)]
  rw [h2, h3] at h5 
  nlinarith