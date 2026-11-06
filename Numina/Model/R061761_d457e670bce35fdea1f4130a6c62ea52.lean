import Mathlib

theorem algebra_21073 {x y : ℝ} (h1 : x^2 + y = 4) (h2 : x^4 + y^2 = 10) :
    x^2 * y = 3 := by
  have hy : y = 4 - x^2 := by
    linarith
  rw [hy] at h2
  have h3 : x^4 + (4 - x^2) ^ 2 = 10 := by
    nlinarith
  have h3' : 2 * x^4 - 8 * x^2 + 6 = 0 := by
    nlinarith
  have h3'' : x^4 - 4 * x^2 + 3 = 0 := by 
    nlinarith
  have h4 : (x^2 - 1) * (x^2 - 3) = 0 := by 
    nlinarith [h3'']
  cases' (mul_eq_zero.mp h4) with h5 h6
  · 
    have hx2 : x^2 = 1 := by 
      linarith
    have hy' : y = 3 := by
      nlinarith [h1, hx2]
    rw [hx2, hy']
    norm_num
  · 
    have hx2 : x^2 = 3 := by 
      linarith 
    have hy' : y = 1 := by 
      nlinarith [h1, hx2]
    rw [hx2, hy']
    norm_num