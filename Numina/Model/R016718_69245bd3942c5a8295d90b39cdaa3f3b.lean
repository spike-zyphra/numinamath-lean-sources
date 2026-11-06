import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_308622 : IsGreatest {x | ∃ t, x = sin (2*t) - 2*(sin t + cos t)} (1 + 2*sqrt 2) := by 
  constructor
  · -- Show 1 + 2√2 is in the set.
    use (5 * Real.pi / 4)
    have h1 : sin (2 * (5 * Real.pi / 4)) = 1 := by
      have h2 : 2 * (5 * Real.pi / 4) = 5 * Real.pi / 2 := by ring
      rw [h2]
      have h3 : 5 * Real.pi / 2 = Real.pi / 2 + 2 * Real.pi := by
        linarith [Real.pi_pos]
      rw [h3]
      have h4 : sin (Real.pi / 2 + 2 * Real.pi) = sin (Real.pi / 2) := by
        rw [sin_add, sin_two_pi, cos_two_pi]
        norm_num
      rw [h4]
      norm_num
    have h2 : sin (5 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
      have h3 : 5 * Real.pi / 4 = Real.pi + Real.pi / 4 := by ring
      rw [h3]
      have h4 : sin (Real.pi + Real.pi / 4) = -sin (Real.pi / 4) := by
        rw [sin_add, sin_pi, cos_pi]
        ring
      rw [h4]
      have h5 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        exact sin_pi_div_four
      rw [h5]
      all_goals ring
    have h3 : cos (5 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
      have h4 : 5 * Real.pi / 4 = Real.pi + Real.pi / 4 := by ring
      rw [h4]
      have h5 : cos (Real.pi + Real.pi / 4) = -cos (Real.pi / 4) := by
        rw [cos_add, sin_pi, cos_pi]
        all_goals ring
      rw [h5]
      have h6 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        exact cos_pi_div_four
      rw [h6]
      all_goals ring
    rw [h1, h2, h3]
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · -- Show that 1 + 2√2 is the greatest
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : sin (2 * t) = 2 * sin t * cos t := by 
      rw [sin_two_mul]
    rw [h1] at ht
    nlinarith [sq_nonneg (sin t + cos t + Real.sqrt 2), sq_nonneg (sin t + cos t - Real.sqrt 2), sq_nonneg (sin t - cos t), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (sin t + cos t - 1), Real.sin_sq_add_cos_sq t]