import Mathlib

theorem algebra_122219 (a b c d e : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hsum : a + b + c + d + e = 8) (hsumsq : a^2 + b^2 + c^2 + d^2 + e^2 = 16) :
    e ≤ 16 / 5 := by 
  have h1 : a + b + c + d = 8 - e := by
    nlinarith
  have h2 : a^2 + b^2 + c^2 + d^2 = 16 - e^2 := by
    nlinarith
  have h3 : (a + b + c + d)^2 ≤ 4 * (a^2 + b^2 + c^2 + d^2) := by
    linarith [sq_nonneg (a + b + c + d), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  rw [h1, h2] at h3
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
          mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]