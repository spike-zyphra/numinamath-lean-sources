import Mathlib

theorem algebra_6192 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : x ^ 2 + y ^ 2 + 49 = 14 * x - 14 * y + 2 * x * y) :
    x - y = 7 := by 
  have h1 : (x - y) ^ 2 + 49 = 14 * (x - y) := by
    linarith [h]

  have h2 : ((x - y) - 7) ^ 2 = 0 := by 
    nlinarith 
  have h3 : (x - y) - 7 = 0 := by 
    rw [sq_eq_zero_iff] at h2
    exact h2 
  linarith