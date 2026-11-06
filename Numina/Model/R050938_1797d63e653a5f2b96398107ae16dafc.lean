import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_312091 :
  IsLeast {x | ∃ t : ℝ, x = sqrt (9 * (t - 3)^2 + (t^2 - 12)^2) +
    sqrt (9 * t^2 + (t^2 - 9 / 4)^2)} (57 / 4) := by
  constructor
  · -- First part: proving 57/4 is in the set
    use 3
    have h1 : sqrt (9 * (3 - 3)^2 + (3^2 - 12)^2) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h2 : sqrt (9 * (3 : ℝ)^2 + (3^2 - 9 / 4)^2) = 1125 / 100 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h1, h2]
    all_goals norm_num
  · -- Second part: proving 57/4 is the least
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : sqrt (9 * (t - 3)^2 + (t^2 - 12)^2) ≥ 0 := by positivity
    have h2 : sqrt (9 * t^2 + (t^2 - 9 / 4)^2) ≥ 0 := by positivity
    by_contra h
    push_neg at h
    have h3 : sqrt (9 * (t - 3)^2 + (t^2 - 12)^2) < 57 / 4 - sqrt (9 * t^2 + (t^2 - 9 / 4)^2) := by linarith
    have h4 : 57 / 4 - sqrt (9 * t^2 + (t^2 - 9 / 4)^2) > 0 := by
      nlinarith [Real.sqrt_nonneg (9 * t^2 + (t^2 - 9 / 4)^2), Real.sqrt_nonneg (9 * (t - 3)^2 + (t^2 - 12)^2), h3]
    have h5 : 9 * (t - 3)^2 + (t^2 - 12)^2 < (57 / 4 - sqrt (9 * t^2 + (t^2 - 9 / 4)^2)) ^ 2 := by
      have h8 : sqrt (9 * (t - 3)^2 + (t^2 - 12)^2) < 57 / 4 - sqrt (9 * t^2 + (t^2 - 9 / 4)^2) := h3
      have h9 : (sqrt (9 * (t - 3)^2 + (t^2 - 12)^2)) ^ 2 < (57 / 4 - sqrt (9 * t^2 + (t^2 - 9 / 4)^2)) ^ 2 := by nlinarith [h8, Real.sqrt_nonneg (9 * (t - 3)^2 + (t^2 - 12)^2), Real.sqrt_nonneg (9 * t^2 + (t^2 - 9 / 4)^2)]
      have h10 : (sqrt (9 * (t - 3)^2 + (t^2 - 12)^2)) ^ 2 = 9 * (t - 3)^2 + (t^2 - 12)^2 := by
        rw [Real.sq_sqrt]
        positivity
      linarith [h10, h9]
    nlinarith [Real.sqrt_nonneg (9 * t^2 + (t^2 - 9 / 4)^2), Real.sq_sqrt (show 0 ≤ (9 * t^2 + (t^2 - 9 / 4)^2 : ℝ) by positivity), Real.sq_sqrt (show 0 ≤ (9 * (t - 3)^2 + (t^2 - 12)^2 : ℝ) by positivity), sq_nonneg (t - 3), sq_nonneg (t^2 - 12), sq_nonneg (t^2 - 9 / 4), sq_nonneg (t^2 - 9), sq_nonneg (t - 3 / 2)]