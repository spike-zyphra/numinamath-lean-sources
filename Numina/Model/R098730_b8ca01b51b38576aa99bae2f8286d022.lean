import Mathlib

theorem algebra_120864 (a b c : ℝ) (h : ∀ x : ℝ, |x| ≤ 1 → |a * x ^ 2 + b * x + c| ≤ 1) :
    ∀ x : ℝ, |x| ≤ 1 → |a * x + b| ≤ 2 := by 
  intro x hx
  have h1 := h 1 (by norm_num)
  have h2 := h (-1) (by norm_num)
  have h3 := h 0 (by norm_num)
  have h4 := h x (by 
    simpa using hx
  )
  cases' abs_le.mp h1 with h1_neg h1_pos
  cases' abs_le.mp h2 with h2_neg h2_pos
  cases' abs_le.mp h3 with h3_neg h3_pos
  cases' abs_le.mp h4 with h4_neg h4_pos
  have hx1 : -1 ≤ x := by linarith [abs_le.mp hx]
  have hx2 : x ≤ 1 := by linarith [abs_le.mp hx]
  have h5 : -2 ≤ a * x + b := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (c - 1), sq_nonneg (c + 1), sq_nonneg (a * (x)), sq_nonneg (b * (x)), sq_nonneg (a * (x - 1)), sq_nonneg (b * (x - 1)), sq_nonneg (a * (x + 1)), sq_nonneg (b * (x + 1))]
  have h6 : a * x + b ≤ 2 := by 
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (c - 1), sq_nonneg (c + 1), sq_nonneg (a * (x)), sq_nonneg (b * (x)), sq_nonneg (a * (x - 1)), sq_nonneg (b * (x - 1)), sq_nonneg (a * (x + 1)), sq_nonneg (b * (x + 1))]
  apply abs_le.mpr
  constructor
  · linarith 
  · linarith