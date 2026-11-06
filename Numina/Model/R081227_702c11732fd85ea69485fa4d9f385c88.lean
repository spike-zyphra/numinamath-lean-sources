import Mathlib

theorem algebra_309741 {a b c : ℝ} (ha : a^2 + b^2 - 4 * a ≤ 1) (hb : b^2 + c^2 - 8 * b ≤ -3)
    (hc : c^2 + a^2 - 12 * c ≤ -26) : (a + b)^c = 27 := by
  have h1 : (a - 1) ^ 2 + (b - 2) ^ 2 + (c - 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 3)]
  have ha1 : (a - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 3)]
  have hb1 : (b - 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 3)]
  have hc1 : (c - 3) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (c - 3)]
  have ha2 : a - 1 = 0 := by 
    rwa [sq_eq_zero_iff] at ha1
  have hb2 : b - 2 = 0 := by 
    rwa [sq_eq_zero_iff] at hb1
  have hc2 : c - 3 = 0 := by 
    rwa [sq_eq_zero_iff] at hc1
  have ha3 : a = 1 := by linarith
  have hb3 : b = 2 := by linarith
  have hc3 : c = 3 := by linarith
  rw [ha3, hb3, hc3]
  norm_num