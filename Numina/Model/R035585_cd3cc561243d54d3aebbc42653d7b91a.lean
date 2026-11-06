import Mathlib

theorem algebra_316831 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 = 4 * a * b * c * d) :
    a = b ∧ b = c ∧ c = d := by

  have h1 : (a - b) ^ 2 + (a - c) ^ 2 + (a - d) ^ 2 + (b - c) ^ 2 + (b - d) ^ 2 + (c - d) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (a ^ 2 - d ^ 2), 
      sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - d ^ 2), sq_nonneg (c ^ 2 - d ^ 2), 
      sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
      sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
      mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
      mul_pos hb hc, mul_pos hb hd, mul_pos hc hd]

  have h2 : a - b = 0 := by
    nlinarith [h1, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
      sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

  have h3 : a - c = 0 := by
    nlinarith [h1, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
      sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

  have h4 : a - d = 0 := by
    nlinarith [h1, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), 
      sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

  constructor
  · -- Prove a = b
    linarith
  constructor
  · -- Prove b = c
    linarith [show a = c by linarith, show a = b by linarith]
  · -- Prove c = d
    linarith [show a = c by linarith, show a = d by linarith]