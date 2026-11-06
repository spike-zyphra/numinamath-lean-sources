import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_203518 :
  IsLeast {k : ℝ | ∀ x y, x * (x - 1) ≤ y * (1 - y) → x ^ 2 + y ^ 2 ≤ k} 2 := by
  constructor
  · -- We need to show that 2 is in the set
    intro x y h
    have h1 : x * (x - 1) ≤ y * (1 - y) := h
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x - y)]
  · -- We need to show that 2 is the least element in the set
    intro k hk
    have h1 := hk 1 1 (by norm_num)
    norm_num at h1 ⊢
    linarith