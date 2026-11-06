import Mathlib

theorem algebra_196591 {a b c : ℝ} (h : ∀ x, |x| ≤ 1 → |a * x ^ 2 + b * x + c| ≤ 1) (x : ℝ) (hx : |x| ≤ 1) : |2 * a * x + b| ≤ 4 := by
  have h1 := h 1 (by norm_num)
  have h2 := h (-1) (by norm_num)
  have h3 := h 0 (by norm_num)
  have h4 := h (1 / 2) (by
    norm_num [abs_le]
  )
  have h5 := h (-1 / 2) (by
    norm_num [abs_le]
  )
  have h6 : -1 ≤ x ∧ x ≤ 1 := by
    constructor
    · linarith [abs_le.mp hx]
    · linarith [abs_le.mp hx]
  have h7 : -1 ≤ x := h6.1
  have h8 : x ≤ 1 := h6.2
  cases' abs_le.mp h1 with h1_neg h1_pos
  cases' abs_le.mp h2 with h2_neg h2_pos
  cases' abs_le.mp h3 with h3_neg h3_pos
  cases' abs_le.mp h4 with h4_neg h4_pos
  cases' abs_le.mp h5 with h5_neg h5_pos
  apply abs_le.mpr
  constructor
  · nlinarith [abs_le.mp hx, h1_neg, h1_pos, h2_neg, h2_pos, h3_neg, h3_pos, h4_neg, h4_pos, h5_neg, h5_pos, mul_self_nonneg (x), mul_self_nonneg (x - 1), mul_self_nonneg (x + 1), mul_self_nonneg (x - 1 / 2), mul_self_nonneg (x + 1 / 2)]
  · nlinarith [abs_le.mp hx, h1_neg, h1_pos, h2_neg, h2_pos, h3_neg, h3_pos, h4_neg, h4_pos, h5_neg, h5_pos, mul_self_nonneg (x), mul_self_nonneg (x - 1), mul_self_nonneg (x + 1), mul_self_nonneg (x - 1 / 2), mul_self_nonneg (x + 1 / 2)]