import Mathlib

theorem inequalities_302631
    (a b c d : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hd : 0 < d)
    (h : a + b + c + d = 4) :
    a^2 * b * c + b^2 * d * a + c^2 * d * a + d^2 * b * c ≤ 4 := by 
  have h1 : a^2 * b * c + b^2 * d * a + c^2 * d * a + d^2 * b * c = (a * b + c * d) * (a * c + b * d) := by 
    ring
  have h2 : (a * b + c * d) * (a * c + b * d) ≤ ((a + d) * (b + c)) ^2 / 4 := by
    nlinarith [sq_nonneg ( (a + d) * (b + c) - 2 * (a * b + c * d) ), sq_nonneg ( (a + d) * (b + c) - 2 * (a * c + b * d) ), sq_nonneg (a * d - b * c), sq_nonneg (a - d), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd ]
  have h4 : (a + d) * (b + c) ≤ 4 := by
    nlinarith [sq_nonneg ( (a + d) - (b + c) ), h, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd ]
  have h3 : (a * b + c * d) * (a * c + b * d) ≤ 4 := by
    nlinarith [sq_nonneg ( (a + d) * (b + c) - 4 ), sq_nonneg ( (a * b + c * d) - (a * c + b * d) ), sq_nonneg (a * d - b * c), sq_nonneg (a - d), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd, h4 ]
  rw [h1] at *
  nlinarith [h3, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd ]