import Mathlib

open Real Set
open scoped Real

theorem inequalities_291062 (t : ℝ) :
  cos t ≤ 3/4 + cos (2*t)/4 ∧ sin t ≤ 3/4 - cos (2*t)/4 := by
  constructor
  · -- Prove the first inequality: cos t ≤ 3/4 + cos (2*t)/4
    have h1 : cos (2 * t) = 2 * cos t ^ 2 - 1 := by
      rw [cos_two_mul]
    rw [h1]
    nlinarith [sq_nonneg (cos t - 1), sq_nonneg (cos t ^ 2 - 1), sq_nonneg (cos t ^ 2 - 1 / 2), Real.cos_sq_add_sin_sq t, sq_nonneg (cos t ^ 2 - 1 / 2)]
  · -- Prove the second inequality: sin t ≤ 3/4 - cos (2*t)/4
    have h2 : cos (2 * t) = 1 - 2 * sin t ^ 2 := by
      rw [cos_two_mul, sin_sq]
      <;> ring_nf <;> simp [sin_sq, cos_sq]
      <;> ring_nf
    rw [h2]
    nlinarith [sq_nonneg (sin t - 1), sq_nonneg (sin t ^ 2 - 1), sq_nonneg (sin t ^ 2 - 1 / 2), Real.sin_sq_add_cos_sq t, sq_nonneg (sin t ^ 2 - 1 / 2)]