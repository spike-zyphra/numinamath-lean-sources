import Mathlib

open Real Set
open scoped Real

theorem inequalities_191587 (α : ℝ) (hα : α ∈ Ioo 0 (π / 2) ∪ Ioo π (3 * π / 2)) :
    |sin (α + π / 4)| > sqrt 2 / 2 := by
  rcases hα with (hα | hα)
  · -- Case 1: α ∈ (0, π/2)
    rcases hα with ⟨hα1, hα2⟩
    have h3 : sin (α + π / 4) = (sin α + cos α) * (sqrt 2 / 2) := by
      rw [sin_add]
      have hsin : sin (π / 4) = sqrt 2 / 2 := by
        rw [sin_pi_div_four]
      have hcos : cos (π / 4) = sqrt 2 / 2 := by
        rw [cos_pi_div_four]
      rw [hsin, hcos]
      all_goals ring
    have h4 : sin α > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hα1, Real.pi_pos]
      linarith [hα2, Real.pi_pos]
    have h5 : cos α > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      linarith [hα1, Real.pi_pos]
      linarith [hα2, Real.pi_pos]
    have h6 : |sin (α + π / 4)| = |(sin α + cos α) * (sqrt 2 / 2)| := by
      rw [h3]
    rw [h6]
    have h8 : sin α + cos α > 1 := by
      nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_pos_of_pos_of_lt_pi (show 0 < α by linarith) (show α < Real.pi by linarith [Real.pi_pos, hα2]), Real.sin_sq_add_cos_sq α, Real.cos_pos_of_mem_Ioo (show α ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [Real.pi_pos, hα1, hα2]), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
    have h7 : (sin α + cos α) * (sqrt 2 / 2) > sqrt 2 / 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
    rw [abs_of_pos (show (sin α + cos α) * (sqrt 2 / 2) > 0 by nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), h4, h5, Real.sin_sq_add_cos_sq α, Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)])]
    all_goals linarith
  · -- Case 2: α ∈ (π, 3π/2)
    rcases hα with ⟨hα1, hα2⟩
    have h3 : sin (α + π / 4) = (sin α + cos α) * (sqrt 2 / 2) := by
      rw [sin_add]
      have hsin : sin (π / 4) = sqrt 2 / 2 := by
        rw [sin_pi_div_four]
      have hcos : cos (π / 4) = sqrt 2 / 2 := by
        rw [cos_pi_div_four]
      rw [hsin, hcos]
      all_goals ring
    have h4 : sin α < 0 := by
      have h8 : α - π > 0 := by linarith
      have h9 : α - π < π / 2 := by
        linarith [Real.pi_pos, hα2]
      have h10 : sin α = -sin (α - π) := by
        rw [show α - π = α - π by ring]
        rw [sin_sub, sin_pi, cos_pi]
        ring
      have h11 : sin (α - π) > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        linarith
        linarith [Real.pi_pos, h9]
      have h12 : sin α < 0 := by
        linarith [h10, h11]
      linarith
    have h5 : cos α < 0 := by
      have h8 : α - π > 0 := by linarith
      have h9 : α - π < π / 2 := by
        linarith [Real.pi_pos, hα2]
      have h10 : cos α = -cos (α - π) := by
        rw [show α - π = α - π by ring]
        rw [cos_sub, sin_pi, cos_pi]
        all_goals ring
      have h11 : cos (α - π) > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        · linarith [Real.pi_pos, h8]
        · linarith [Real.pi_pos, h9]
      have h12 : cos α < 0 := by
        linarith [h10, h11]
      linarith
    have h6 : |sin (α + π / 4)| = |(sin α + cos α) * (sqrt 2 / 2)| := by
      rw [h3]
    rw [h6]
    have h8 : sin α + cos α < -1 := by
      nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq α, Real.sin_pos_of_pos_of_lt_pi (show 0 < α - π by linarith) (show α - π < Real.pi by linarith [Real.pi_pos, hα2]), Real.cos_pos_of_mem_Ioo (show α - π ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [Real.pi_pos, hα1, hα2]), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
    have h7 : (sin α + cos α) * (sqrt 2 / 2) < - (sqrt 2 / 2) := by
      nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
    rw [abs_of_neg (by nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)])]
    all_goals nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]