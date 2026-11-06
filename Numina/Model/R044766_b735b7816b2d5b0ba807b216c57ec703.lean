import Mathlib

theorem algebra_199676 {x y : ℝ} (h1 : x^3 + y^3 = 7) (h2 : x + x * y + y = -1) :
    (x, y) = (-1, 2) ∨ (x, y) = (2, -1) := by
  have h3 : (x + 1) * (y + 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h3) with h4 h5
  · -- Case where x + 1 = 0, so x = -1
    have hx : x = -1 := by linarith
    have hy : y = 2 := by
      rw [hx] at h1 
      have h1' : (-1 : ℝ) ^ 3 + y ^ 3 = 7 := by linarith 
      have h2' : y ^ 3 = 8 := by 
        nlinarith 
      have h4 : y = 2 := by 
        have h5 : y ^ 3 - 8 = 0 := by linarith 
        have h6 : (y - 2) * (y ^ 2 + 2 * y + 4) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.1 h6) with h7 h8 
        · -- y - 2 = 0 
          linarith 
        · -- y^2 + 2 * y + 4 = 0
          nlinarith [sq_nonneg (y + 1)]
      assumption
    left 
    simp [hx, hy]
  · -- Case where y + 1 = 0, so y = -1
    have hy : y = -1 := by linarith
    have hx : x = 2 := by
      rw [hy] at h1
      have h1' : x ^ 3 + (-1 : ℝ) ^ 3 = 7 := by linarith
      have h2' : x ^ 3 = 8 := by
        nlinarith
      have h4 : x = 2 := by
        have h5 : x ^ 3 - 8 = 0 := by linarith 
        have h6 : (x - 2) * (x ^ 2 + 2 * x + 4) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.1 h6) with h7 h8 
        · -- x - 2 = 0 
          linarith 
        · -- x^2 + 2 * x + 4 = 0 
          nlinarith [sq_nonneg (x + 1)]
      assumption
    right 
    simp [hx, hy]