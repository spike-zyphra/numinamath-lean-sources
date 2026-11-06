import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_310099 : IsGreatest {x | ∃ t, x = 7 * sin t + sin (2 * t)} (15 * sqrt 15 / 8) := by
  constructor
  · -- Show 15 * sqrt 15 / 8 is in the set
    use (Real.arccos (1 / 4))
    have h1 : sin (Real.arccos (1 / 4)) = Real.sqrt 15 / 4 := by
      have h2 : sin (Real.arccos (1 / 4)) = Real.sqrt (1 - (1 / 4) ^ 2) := by
        rw [sin_arccos]
      rw [h2]
      have h3 : (1 - (1 / 4) ^ 2 : ℝ) = (15 / 16 : ℝ) := by norm_num
      rw [h3]
      have h4 : Real.sqrt (15 / 16 : ℝ) = Real.sqrt 15 / 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf <;> norm_num
      rw [h4]
    have h2 : sin (2 * (Real.arccos (1 / 4))) = Real.sqrt 15 / 8 := by
      have h3 : sin (2 * (Real.arccos (1 / 4))) = 2 * sin (Real.arccos (1 / 4)) * cos (Real.arccos (1 / 4)) := by
        rw [sin_two_mul]
      rw [h3]
      rw [h1]
      have h4 : cos (Real.arccos (1 / 4)) = (1 / 4 : ℝ) := by
        apply Real.cos_arccos
        all_goals norm_num
      rw [h4]
      field_simp
      ring_nf
    linarith [h1, h2]
  · -- Show it's the greatest
    intro x hx
    rcases hx with ⟨t, ht⟩
    rw [ht]
    have h3 : sin t ^ 2 + cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
    have h4 : sin (2 * t) = 2 * sin t * cos t := by
      rw [sin_two_mul]
    rw [h4]
    nlinarith [sq_nonneg (sin t ^ 2 + cos t ^ 2 - 1),
        sq_nonneg (cos t - 1 / 4),
        sq_nonneg (sin t ^ 2 - 15 / 16),
        sq_nonneg (7 + 2 * cos t),
        sq_nonneg (sin t - Real.sqrt 15 / 4),
        sq_nonneg (sin t + Real.sqrt 15 / 4),
        Real.sqrt_pos.mpr (show (0 : ℝ) < 15 by norm_num),
        Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num),
        sq_nonneg (cos t ^ 2 - 1 / 16)]