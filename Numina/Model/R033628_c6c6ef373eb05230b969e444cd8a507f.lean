import Mathlib


lemma lemma_1 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b * c + b * c * d + c * d * a + d * a * b = 4) :
    4 ≤ a + b + c + d := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d),
          mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd,
          mul_pos (mul_pos ha hb) hc, mul_pos (mul_pos ha hb) hd, mul_pos (mul_pos ha hc) hb, mul_pos (mul_pos ha hc) hd, mul_pos (mul_pos hb hc) ha, mul_pos (mul_pos hb hc) hd, mul_pos (mul_pos hb ha) hc, mul_pos (mul_pos hb ha) hc, mul_pos (mul_pos hc ha) hb, mul_pos (mul_pos hc ha) hb]


theorem inequalities_92074 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b * c + b * c * d + c * d * a + d * a * b = 4) :
    4 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  have h1 : 4 ≤ a + b + c + d := by
    apply lemma_1 a b c d ha hb hc hd h
  have h2 : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    linarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]
  have h3 : (a + b + c + d) ^ 2 ≥ 16 := by
    nlinarith
  nlinarith