import Mathlib

theorem algebra_22003 {x : ℝ} (hx : x ≠ -1) (h : x^5 + 5 * x^4 + 10 * x^3 + 10 * x^2 - 5 * x + 1 = 10) :
    (x + 1)^4 = 10 := by 
  have h1 : (x + 1) ^ 5 - 10 * x - 10 = 0 := by 
    nlinarith 
  have h3 : (x + 1) ^ 5 - 10 * x - 10 = (x + 1) * ((x + 1) ^ 4 - 10) := by 
    ring 
  rw [h3] at h1 
  cases' (mul_eq_zero.mp h1) with h4 h5 
  · -- Case where x+1 = 0, so x = -1, which contradicts
    have h6 : x + 1 = 0 := by linarith
    have h7 : x = -1 := by linarith
    contradiction 
  · -- Case where (x+1)^4 - 10 = 0, so (x+1)^4 = 10
    linarith