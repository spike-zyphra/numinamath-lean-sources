import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_164778 (a b c : ℝ) (h : ∀ x ∈ Icc 0 1, |a * x^2 + b * x + c| ≤ 1) :
    2 * |a| + sqrt 2 * |b| + |c| ≤ 17 + 8 * sqrt 2 := by 
  have h1 := h 0 (by norm_num)
  have h2 := h 1 (by norm_num)
  have h3 := h (1 / 2) (by norm_num)
  have h4 := h (2 / 3) (by norm_num)
  have h5 := h (1 / 3) (by norm_num)
  cases' abs_le.mp h1 with h1_neg h1_pos
  cases' abs_le.mp h2 with h2_neg h2_pos
  cases' abs_le.mp h3 with h3_neg h3_pos
  cases' abs_le.mp h4 with h4_neg h4_pos
  cases' abs_le.mp h5 with h5_neg h5_pos
  cases' abs_cases a with ha1 ha1 <;> cases' abs_cases b with hb1 hb1 <;> cases' abs_cases c with hc1 hc1
  <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)]