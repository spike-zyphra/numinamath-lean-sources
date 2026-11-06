import Mathlib

open Real Set
open scoped Real

theorem algebra_187107 (α : Real) (hα : α ∈ Ioo (π/4) (π/2)) :
    (cos α)^(sin α) < (cos α)^(cos α) ∧ (cos α)^(cos α) < (sin α)^(cos α) := by
  rcases hα with ⟨hα1, hα2⟩
  have h1 : cos α < sin α := by
    have h2 : sin α > cos α := by
      have h3 : α > π / 4 := by linarith
      have h4 : α - π / 4 > 0 := by linarith
      have h5 : sin α - cos α > 0 := by
        -- Use angle addition formula to show sin α - cos α = sqrt(2) * sin(α - π / 4)
        have h6 : sin α - cos α = Real.sqrt 2 * sin (α - (π / 4)) := by
          have h7 : sin (α - (π / 4)) = sin α * cos (π / 4) - cos α * sin (π / 4) := by 
            rw [sin_sub]
          have h8 : cos (π / 4) = Real.sqrt 2 / 2 := by
            rw [cos_pi_div_four]
          have h9 : sin (π / 4) = Real.sqrt 2 / 2 := by
            rw [sin_pi_div_four]
          rw [h7, h8, h9]
          ring_nf
          <;> simp [Real.sqrt_sq]
          <;> ring_nf
        have h8 : α - (π / 4) > 0 := by 
          linarith
        have h9 : sin (α - (π / 4)) > 0 := by 
          apply sin_pos_of_pos_of_lt_pi
          all_goals
          linarith [hα1, Real.pi_pos, h8, hα2]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), h9]
      linarith
    linarith
  constructor
  · -- Prove that (cos α)^(sin α) < (cos α)^(cos α)
    have h2 : 0 < cos α := by
      apply cos_pos_of_mem_Ioo
      constructor
      linarith [hα1, hα2, Real.pi_pos]
      linarith [hα1, hα2, Real.pi_pos]
    have h3 : cos α < 1 := by
      have h4 : cos α < cos (0 : ℝ) := by
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals linarith [hα1, hα2, Real.pi_pos]
      have h5 : cos (0 : ℝ) = 1 := by 
        rw [cos_zero]
      linarith [h5, h4]
    have h4 : sin α > cos α := h1
    have h5 : (cos α) ^ (sin α) < (cos α) ^ (cos α) := by
      apply Real.rpow_lt_rpow_of_exponent_gt
      all_goals nlinarith [h2, h3, h4, Real.sin_sq_add_cos_sq α]
    linarith
  · -- Prove that (cos α)^(cos α) < (sin α)^(cos α)
    have h2 : cos α < sin α := h1
    have h3 : 0 < cos α := by
      apply cos_pos_of_mem_Ioo
      constructor 
      linarith [hα1, hα2, Real.pi_pos]
      linarith [hα1, hα2, Real.pi_pos]
    have h4 : (cos α) ^ (cos α) < (sin α) ^ (cos α) := by
      apply Real.rpow_lt_rpow
      all_goals nlinarith [h2, Real.sin_pos_of_pos_of_lt_pi (show 0 < α by linarith [hα1, Real.pi_pos]) (show α < Real.pi by linarith [hα2, Real.pi_pos]), Real.sin_sq_add_cos_sq α]
    linarith