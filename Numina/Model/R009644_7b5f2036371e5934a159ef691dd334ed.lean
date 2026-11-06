import Mathlib

theorem algebra_10710 {x k : ℝ} (h : (x^2 - k) * (x + k) = x^3 + k * (x^2 - x - 5)) (hk : k ≠ 0) :
    k = 5 := by
  have eq1 : (x ^ 2 - k) * (x + k) = x ^ 3 + k * x ^ 2 - k * x - k ^ 2 := by
    ring
  have eq2 : x^3 + k * (x^2 - x - 5) = x^3 + k * x^2 - k * x - 5 * k := by 
    ring
  rw [eq1, eq2] at h
  have eq3 : -k^2 = -5 * k := by 
    linarith [h]
  have eq4 : k^2 - 5 * k = 0 := by 
    linarith [eq3]
  have h5 : k * (k - 5) = 0 := by 
    linarith [eq4]
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case k = 0, which contradicts the hypothesis
    exfalso
    exact hk h6
  · -- Case k - 5 = 0, which means k = 5
    linarith