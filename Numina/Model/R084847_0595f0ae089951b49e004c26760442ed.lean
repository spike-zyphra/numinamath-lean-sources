import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_293288 (x : ℝ) :
  -4 ≤ cos (2 * x) + 3 * sin x ∧ cos (2 * x) + 3 * sin x ≤ 17 / 8 := by
  have h1 : cos (2 * x) = 1 - 2 * sin x ^ 2 := by
    rw [cos_two_mul]
    rw [sin_sq]
    ring
  have h2 : -1 ≤ sin x ∧ sin x ≤ 1 := by
    apply sin_mem_Icc
  have h3 : -4 ≤ cos (2 * x) + 3 * sin x := by
    rw [h1]
    nlinarith [sq_nonneg (sin x + 1), sq_nonneg (sin x - 1), sq_nonneg (sin x - 3 / 4)]
  have h4 : cos (2 * x) + 3 * sin x ≤ 17 / 8 := by
    rw [h1]
    nlinarith [sq_nonneg (sin x - 3 / 4), sq_nonneg (sin x - 1), sq_nonneg (sin x + 1)]
  constructor
  · linarith
  · linarith