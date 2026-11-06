import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_302743 (p q : ℝ) (h : ∀ x ∈ Icc (-1) 1, 2*p*x^2+q*x-p+1 ≥ 0) :
    p+q ≤ 2 := by
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have hm1 := h (-1) (by norm_num)
  have h1_2 := h (1/2) (by
    norm_num [mem_Icc]
    <;> norm_num
  )
  have h2_1 := h (-1/2) (by
    norm_num [mem_Icc]
    <;> norm_num
  )
  nlinarith [sq_nonneg (p - q), sq_nonneg (p + q - 1), sq_nonneg (q - 1), sq_nonneg (p - 1)]