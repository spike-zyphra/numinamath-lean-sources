import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_136668 (C : ℝ) :
  (∀ x > 0, ∀ y ≥ 4 * x, x ^ 2 + y ^ 2 ≥ C * x * y) ↔
  C ≤ 17 / 4 := by
  constructor
  · -- Forward: if the inequality holds for all x > 0 and y ≥ 4x, then C ≤ 17/4
    intro h
    have h1 : (1 : ℝ) ^ 2 + (4 : ℝ) ^ 2 ≥ C * (1 : ℝ) * (4 : ℝ) := by
      specialize h 1 (by norm_num) 4 (by norm_num)
      simpa using h
    nlinarith
  · -- Backward: if C ≤ 17/4, then inequality holds for all x > 0 and y ≥ 4x
    intro h x hx y hy
    have h4 : x * y > 0 := by
      have hx_pos : x > 0 := hx
      have hy_pos : y > 0 := by nlinarith
      positivity
    nlinarith [sq_nonneg (y - 4 * x), sq_nonneg (y - 16 * x), sq_nonneg (y - 2 * x), sq_nonneg (x - y / 4), mul_pos hx (show 0 < y by linarith), mul_pos hx (show y > 0 by linarith), h]