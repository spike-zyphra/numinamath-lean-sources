import Mathlib

theorem algebra_22195 (x y : ℤ) (h : (x - 5) ^ 2 + (y - 15) ^ 2 = 130) (h' : x = 2 * y) :
    x ≤ 12 := by 
  rw [show x = 2 * y by linarith] at h 
  have h_eq : (y - 4) * (y - 6) = 0 := by
    ring_nf at h 
    nlinarith 
  cases' (mul_eq_zero.1 h_eq) with h4 h6
  · -- Case where y = 4
    have hy4 : y = 4 := by linarith 
    have hx8 : x = 8 := by 
      linarith [h', hy4] 
    omega 
  · -- Case where y = 6
    have hy6 : y = 6 := by linarith 
    have hx12 : x = 12 := by 
      linarith [h', hy6] 
    omega