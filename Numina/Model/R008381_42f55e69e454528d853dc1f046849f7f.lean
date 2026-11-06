import Mathlib

theorem algebra_91553 {x y z : ℝ} (h1 : x + y = 2) (h2 : x * y = z ^ 2 + 1) :
    x ^ 2 + y ^ 2 + z ^ 2 = 2 := by
  have h3 : y = 2 - x := by
    linarith
  rw [h3] at h2
  have h4 : (x - 1) ^ 2 + z ^ 2 = 0 := by 
    nlinarith
  have hx1 : (x - 1) ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg z]
  have hz1 : z ^ 2 = 0 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg z]
  have hx : x - 1 = 0 := by
    rw [sq_eq_zero_iff] at hx1 
    linarith 
  have hz : z = 0 := by 
    rw [sq_eq_zero_iff] at hz1 
    linarith 
  have hx2 : x = 1 := by linarith 
  have hy2 : y = 1 := by 
    nlinarith [hx2, show x + y = 2 from h1]
  rw [hx2, hy2, hz]
  norm_num 
  <;> nlinarith