import Mathlib

theorem algebra_322560 {x y : ℝ} (h₀ : x + y = 3) (h₁ : x ^ 2 + y ^ 2 - x * y = 4) :
    x ^ 4 + y ^ 4 + x ^ 3 * y + x * y ^ 3 = 36 := by
  have h2 : x * y = 5 / 3 := by
    have h3 : (x + y) ^ 2 - 3 * (x * y) = 4 := by
      nlinarith [h₁, h₀]
    rw [show (x + y) ^ 2 = 9 by nlinarith [h₀]] at h3
    linarith
  have h4 : x ^ 2 + y ^ 2 = 17 / 3 := by 
    nlinarith [h₁, h2]
  have h5 : x ^ 4 + y ^ 4 = (x ^ 2 + y ^ 2) ^ 2 - 2 * (x * y) ^ 2 := by 
    ring
  have h6 : x ^ 3 * y + x * y ^ 3 = (x * y) * (x ^ 2 + y ^ 2) := by 
    ring
  calc
    x ^ 4 + y ^ 4 + x ^ 3 * y + x * y ^ 3 
        = (x ^ 4 + y ^ 4) + (x ^ 3 * y + x * y ^ 3) := by ring
    _ = ((x ^ 2 + y ^ 2) ^ 2 - 2 * (x * y) ^ 2) + ((x * y) * (x ^ 2 + y ^ 2)) := by
      rw [h5, h6]
    _ = ((17 / 3) ^ 2 - 2 * (5 / 3) ^ 2) + ((5 / 3) * (17 / 3)) := by
      rw [h4, h2]
    _ = 36 := by
      norm_num