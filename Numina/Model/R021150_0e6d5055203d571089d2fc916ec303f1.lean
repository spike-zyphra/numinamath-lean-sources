import Mathlib

theorem inequalities_603612 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    6 * (a^3 + b^3 + c^3 + d^3) ≥ (a^2 + b^2 + c^2 + d^2) + 1 / 8 := by
  have h1 : a + b + c + d = 1 := h
  have h2 : a^2 + b^2 + c^2 + d^2 = (a + b + c + d) ^ 2 - 2 * (a*b + a*c + a*d + b*c + b*d + c*d) := by
    nlinarith
  have h3 : a^3 + b^3 + c^3 + d^3 = (a + b + c + d) ^ 3 - 3 * (a + b + c + d) * (a*b + a*c + a*d + b*c + b*d + c*d) + 3 * (a*b*c + a*b*d + a*c*d + b*c*d) := by
    ring
  rw [h] at h3
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
            sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
            sq_nonneg (a + b - c - d), sq_nonneg (a - b + c - d), 
            sq_nonneg (a - b - c + d), 
            mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
            mul_pos hb hc, mul_pos hb hd, 
            mul_pos hc hd ]