import Mathlib

theorem algebra_297094 {x y z : ℝ} (h : 4*x-3*y-6*z=0) (h' : x+2*y-7*z=0) (h'' : x*y*z≠0) :
    (2*x^2+3*y^2+6*z^2)/(x^2+5*y^2+7*z^2) = 1 := by
  have h1 : y = 2 * z := by 
    nlinarith [h, h']
  have h2 : x = 3 * z := by
    rw [h1] at h'
    nlinarith
  have h3 : 2 * x ^ 2 + 3 * y ^ 2 + 6 * z ^ 2 = 36 * z ^ 2 := by 
    rw [h2, h1]
    nlinarith
  have h4 : x ^ 2 + 5 * y ^ 2 + 7 * z ^ 2 = 36 * z ^ 2 := by 
    rw [h2, h1]
    nlinarith
  have eq1 : 2 * x ^ 2 + 3 * y ^ 2 + 6 * z ^ 2 = x ^ 2 + 5 * y ^ 2 + 7 * z ^ 2 := by 
    linarith [h3, h4]
  have hz : z ≠ 0 := by
    by_contra hz0
    have hz0' : z = 0 := hz0
    have hy0 : y = 0 := by 
      rw [hz0'] at h1
      nlinarith
    have hx0 : x = 0 := by 
      rw [hz0'] at h2
      nlinarith
    have hxyz : x * y * z = 0 := by 
      simp [hx0, hy0, hz0']
    contradiction
  have h7 : x ^ 2 + 5 * y ^ 2 + 7 * z ^ 2 ≠ 0 := by
    by_contra h0
    have h0' : x ^ 2 + 5 * y ^ 2 + 7 * z ^ 2 = 0 := by linarith
    have hx2 : x ^ 2 ≥ 0 := by nlinarith
    have hy2 : y ^ 2 ≥ 0 := by nlinarith
    have hz2 : z ^ 2 ≥ 0 := by nlinarith 
    have hx2' : x ^ 2 = 0 := by
      linarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
    have hy2' : y ^ 2 = 0 := by 
      linarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
    have hz2' : z ^ 2 = 0 := by 
      linarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
    have hx0 : x = 0 := by 
      nlinarith
    have hy0 : y = 0 := by 
      nlinarith
    have hz0 : z = 0 := by 
      nlinarith
    have hxyz : x * y * z = 0 := by 
      simp [hx0, hy0, hz0]
    contradiction
  have eq2 : (2 * x ^ 2 + 3 * y ^ 2 + 6 * z ^ 2) / (x ^ 2 + 5 * y ^ 2 + 7 * z ^ 2) = 1 := by 
    rw [show 2 * x ^ 2 + 3 * y ^ 2 + 6 * z ^ 2 = x ^ 2 + 5 * y ^ 2 + 7 * z ^ 2 by linarith [eq1]]
    field_simp [h7]
  linarith