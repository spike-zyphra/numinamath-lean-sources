import Mathlib

open Real Set
open scoped Real

theorem inequalities_315183 (α : ℝ) (hα : α ∈ Icc (π/4) (π/2)) :
    (1 + sin α - cos α)/sin α ≥ sqrt 2 := by
  rcases hα with ⟨hα1, hα2⟩

  have h3 : 1 + sin α - cos α ≥ sqrt 2 * sin α := by
    have h5 : cos α ≤ sqrt 2 / 2 := by
      have h6 : cos α ≤ cos (π / 4) := by
        apply Real.cos_le_cos_of_nonneg_of_le_pi
        all_goals linarith [hα1, hα2, Real.pi_pos]
      have h7 : cos (π / 4) = sqrt 2 / 2 := Real.cos_pi_div_four
      linarith [h7]
    
    have h8 : sin α ≥ sqrt 2 / 2 := by
      have h9 : sin α ≥ sin (π / 4) := by
        apply Real.sin_le_sin_of_le_of_le_pi_div_two
        all_goals linarith [hα1, hα2, Real.pi_pos]
      have h10 : sin (π / 4) = sqrt 2 / 2 := Real.sin_pi_div_four
      linarith [h10]

    nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), 
        Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), 
        Real.sin_sq_add_cos_sq α, 
        mul_nonneg (show (0 : ℝ) ≤ (sqrt 2 / 2) by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]) 
          (show (0 : ℝ) ≤ (sqrt 2 / 2) by nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)])]
  
  have h3' : sin α > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [show π / 4 > 0 by linarith [Real.pi_pos], hα1]
    linarith [hα2, Real.pi_pos]

  have h14 : (1 + sin α - cos α) / sin α ≥ sqrt 2 := by
    apply (le_div_iff₀ (by linarith [h3'])).mpr
    linarith [h3]
  linarith [h14]