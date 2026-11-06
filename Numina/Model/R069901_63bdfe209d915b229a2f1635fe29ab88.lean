import Mathlib

theorem algebra_22408 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : a + b + c + d = 1) :
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 1 / 4 := by 
  have h1 : (a - 1 / 4) ^ 2 + (b - 1 / 4) ^ 2 + (c - 1 / 4) ^ 2 + (d - 1 / 4) ^ 2 ≥ 0 := by
    apply add_nonneg
    apply add_nonneg
    apply add_nonneg
    · apply sq_nonneg
    · apply sq_nonneg
    · apply sq_nonneg
    · apply sq_nonneg
  nlinarith [h, sq_nonneg (a - 1 / 4), sq_nonneg (b - 1 / 4), sq_nonneg (c - 1 / 4), sq_nonneg (d - 1 / 4)]