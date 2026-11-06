import Mathlib

theorem inequalities_599917 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    6 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) ≥ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 1 / 8 := by

  have h₁ : 6 * (a ^ 3) - a ^ 2 ≥ 5 / 8 * a - 1 / 8 := by
    nlinarith [sq_nonneg (a - 1 / 4), sq_nonneg (a * 4 - 1), sq_nonneg (a - 1 / 4), sq_nonneg ((a - 1 / 4) * (a - 1 / 4)), sq_nonneg ((a * 4 - 1) * (a * 4 - 1)), mul_pos ha (show 0 < 1 from by norm_num)]
  have h₂ : 6 * (b ^ 3) - b ^ 2 ≥ 5 / 8 * b - 1 / 8 := by 
    nlinarith [sq_nonneg (b - 1 / 4), sq_nonneg (b * 4 - 1), sq_nonneg (b - 1 / 4), sq_nonneg ((b - 1 / 4) * (b - 1 / 4)), sq_nonneg ((b * 4 - 1) * (b * 4 - 1)), mul_pos hb (show 0 < 1 from by norm_num)]
  have h₃ : 6 * (c ^ 3) - c ^ 2 ≥ 5 / 8 * c - 1 / 8 := by
    nlinarith [sq_nonneg (c - 1 / 4), sq_nonneg (c * 4 - 1), sq_nonneg (c - 1 / 4), sq_nonneg ((c - 1 / 4) * (c - 1 / 4)), sq_nonneg ((c * 4 - 1) * (c * 4 - 1)), mul_pos hc (show 0 < 1 from by norm_num)]
  have h₄ : 6 * (d ^ 3) - d ^ 2 ≥ 5 / 8 * d - 1 / 8 := by
    nlinarith [sq_nonneg (d - 1 / 4), sq_nonneg (d * 4 - 1), sq_nonneg (d - 1 / 4), sq_nonneg ((d - 1 / 4) * (d - 1 / 4)), sq_nonneg ((d * 4 - 1) * (d * 4 - 1)), mul_pos hd (show 0 < 1 from by norm_num)]

  have h₅ : 6 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≥ 1 / 8 := by
    linarith [h₁, h₂, h₃, h₄, h]

  linarith [h₅]