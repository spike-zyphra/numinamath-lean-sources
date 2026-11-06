import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_104363 (a b : ℝ) :
  (∀ x ∈ Icc 1 2, |a * x^2 + b * x + a| ≤ x) → 3 * a + b ≤ 3 := by
  intro h
  have h1 := h 1 (left_mem_Icc.mpr (by norm_num))
  have h2 := h 2 (right_mem_Icc.mpr (by norm_num))
  norm_num at h1 h2
  
  cases' abs_le.mp h1 with h1_neg h1_pos
  cases' abs_le.mp h2 with h2_neg h2_pos
  
  linarith