import Mathlib

theorem algebra_11672 {x : ℝ} (hx : x ≠ 0) (h : x^3 + 1/x^3 = 52) :
    x + 1/x = 4 := by 
  have h1 : x^3 + 1 / x^3 = (x + 1 / x) ^ 3 - 3 * (x + 1 / x) := by
    field_simp
    ring
  
  rw [h1] at h
  
  have h2 : (x + 1 / x) ^ 3 - 3 * (x + 1 / x) - 52 = 0 := by linarith
  
  have h3 : (x + 1 / x - 4) * ((x + 1 / x) ^ 2 + 4 * (x + 1 / x) + 13) = 0 := by
    ring_nf at h2 ⊢
    linarith
  
  cases' (mul_eq_zero.mp h3) with h4 h5
  
  · -- Case where x + 1/x - 4 = 0, so x + 1/x = 4
    linarith
  
  · -- Case where (x + 1/x)^2 + 4*(x + 1/x) + 13 = 0
    have h6 : (x + 1 / x) ^ 2 + 4 * (x + 1 / x) + 13 = 0 := by linarith
  
    have h7 : (x + 1 / x) ^ 2 + 4 * (x + 1 / x) + 13 > 0 := by
      nlinarith [sq_nonneg (x + 1 / x + 2)]
  
    linarith