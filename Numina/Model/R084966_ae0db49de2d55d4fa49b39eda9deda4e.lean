import Mathlib

theorem inequalities_257678 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hord : a > b ∧ b > c ∧ c > d) :
    (a + b + c + d)^2 > a^2 + 3 * b^2 + 5 * c^2 + 7 * d^2 := by
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd,
    sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, sq_pos_of_pos hd,
    hord.left, hord.right.left, hord.right.right]