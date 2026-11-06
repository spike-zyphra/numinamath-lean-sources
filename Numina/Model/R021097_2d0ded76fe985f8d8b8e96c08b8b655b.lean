import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_251089 :
  IsLeast {y : ℝ | ∃ x, y = sqrt (9 * (x - 3)^2 + (x^2 - 12)^2) +
    sqrt (9 * x^2 + (x^2 - 9 / 4)^2)} (57 / 4) := by
  constructor
  · -- Show that 57/4 is in the set.
    use 3
    have h1 : sqrt (9 * (3 - 3 : ℝ) ^ 2 + (3 ^ 2 - 12) ^ 2) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    have h2 : sqrt (9 * (3 : ℝ) ^ 2 + (3 ^ 2 - 9 / 4) ^ 2) = 45 / 4 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    rw [h1, h2]
    norm_num
  · -- Show that 57/4 is the least element in the set.
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h4 : sqrt (9 * (x - 3) ^ 2 + (x^2 - 12) ^ 2) + sqrt (9 * x^2 + (x^2 - 9 / 4) ^ 2) ≥ 57 / 4 := by
      have h5 : sqrt (9 * (x - 3) ^ 2 + (x^2 - 12) ^ 2) ≥ 0 := by positivity
      have h6 : sqrt (9 * x^2 + (x^2 - 9 / 4) ^ 2) ≥ 0 := by positivity
      have h7 : (sqrt (9 * (x - 3) ^ 2 + (x^2 - 12) ^ 2) + sqrt (9 * x^2 + (x^2 - 9 / 4) ^ 2)) ^ 2 ≥ (57 / 4) ^ 2 := by
        have h8 : sqrt (9 * (x - 3) ^ 2 + (x^2 - 12) ^ 2) ^ 2 = 9 * (x - 3) ^ 2 + (x^2 - 12) ^ 2 := Real.sq_sqrt (by positivity)
        have h9 : sqrt (9 * x^2 + (x^2 - 9 / 4) ^ 2) ^ 2 = 9 * x^2 + (x^2 - 9 / 4) ^ 2 := Real.sq_sqrt (by positivity)
        have h10 : sqrt (9 * (x - 3) ^ 2 + (x^2 - 12) ^ 2) * sqrt (9 * x^2 + (x^2 - 9 / 4) ^ 2) ≥ 0 := by positivity
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 9 * (x - 3) ^ 2 + (x^2 - 12) ^ 2 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ 9 * x^2 + (x^2 - 9 / 4) ^ 2 by positivity), sq_nonneg (x ^ 2 - 9 / 4), sq_nonneg (x ^ 2 - 12), sq_nonneg (x - 3 / 2), sq_nonneg (x ^ 2 - 9), sq_nonneg (x), sq_nonneg (x - 3), mul_nonneg (Real.sqrt_nonneg (9 * (x - 3) ^ 2 + (x^2 - 12) ^ 2)) (Real.sqrt_nonneg (9 * x^2 + (x^2 - 9 / 4) ^ 2))]
      nlinarith [Real.sqrt_nonneg (9 * (x - 3) ^ 2 + (x^2 - 12) ^ 2), Real.sqrt_nonneg (9 * x^2 + (x^2 - 9 / 4) ^ 2), h7, mul_nonneg (Real.sqrt_nonneg (9 * (x - 3) ^ 2 + (x^2 - 12) ^ 2)) (Real.sqrt_nonneg (9 * x^2 + (x^2 - 9 / 4) ^ 2))]
    linarith [hx, h4]