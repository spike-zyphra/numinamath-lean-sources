import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_11463 (a b c d : ℝ) (ha : a ≠ 0)
  (h : ∀ x ∈ Icc 0 1, |(3*a)*x^2 + 2*b*x + c| ≤ 1) :
  a ≤ 8/3 := by
  have h1 := h 0 (by norm_num)
  have h2 := h 1 (by norm_num)
  have h3 := h (1/2) (by norm_num [mem_Icc])
  have h4 := h (1/4) (by norm_num [mem_Icc])
  have h5 := h (3/4) (by norm_num [mem_Icc])
  have h6 := h (2/3) (by norm_num [mem_Icc])
  -- Compute f'(0/4)
  cases' abs_le.mp h1 with h1_a h1_b
  -- Compute f'(1/1)
  cases' abs_le.mp h2 with h2_a h2_b
  -- Compute f'(1/2) 
  cases' abs_le.mp h3 with h3_a h3_b
  cases' abs_le.mp h4 with h4_a h4_b
  cases' abs_le.mp h5 with h5_a h5_b
  cases' abs_le.mp h6 with h6_a h6_b
  norm_num at h1_a h1_b h2_a h2_b h3_a h3_b h4_a h4_b h5_a h5_b h6_a h6_b
  nlinarith [sq_nonneg (a - 8/3), sq_nonneg (b - 4/3), sq_nonneg (c - 4/3), sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (b - a), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (b * 2), sq_nonneg (c * 2), sq_nonneg (a * 2 - b), sq_nonneg (b * 2 - c), sq_nonneg (c * 4 - a * 3)
]