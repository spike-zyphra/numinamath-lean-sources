import Mathlib

open Real Set
open scoped Real

theorem inequalities_251028 (α : ℝ) (hα : α ∈ Ioo 0 (π / 4)) :
    sin (2 * α) < 2 * sin α := by
  rcases hα with ⟨hα1, hα2⟩
  have h1 : sin (2 * α) = 2 * sin α * cos α := by 
    rw [sin_two_mul]
  rw [h1]
  have h2 : 0 < sin α := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hα1, hα2, Real.pi_pos, Real.pi_gt_three]
    linarith [hα1, hα2, Real.pi_pos, Real.pi_gt_three]
  have h3 : cos α < 1 := by
    have h4 : cos α < cos (0 : ℝ) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals
        linarith [hα1, hα2, Real.pi_pos, Real.pi_gt_three]
    have h5 : cos (0 : ℝ) = 1 := Real.cos_zero
    linarith [h4, h5]
  have h6 : cos α - 1 < 0 := by linarith
  nlinarith [Real.sin_pos_of_pos_of_lt_pi hα1 (show α < Real.pi by linarith [hα2, Real.pi_pos, Real.pi_gt_three]), Real.cos_sq_add_sin_sq α, mul_pos (show 0 < sin α by linarith) (show 0 < sin α by linarith), h6]