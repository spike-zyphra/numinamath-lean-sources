import Mathlib

open Real Set
open scoped Real

theorem inequalities_272389 (α : Real) (hα : α ∈ Ioo 0 (π/2)) :
    IsLeast {x | ∃ α : Real, α ∈ Ioo 0 (π/2) ∧ x = (sin α)^3 / cos α + (cos α)^3 / sin α} 1 := by
  constructor
  · -- Show 1 is in the set
    use Real.pi / 4
    constructor
    · -- Show that π/4 ∈ (0, π/2)
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Show the value is 1
      have h1 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [sin_pi_div_four]
      have h2 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [cos_pi_div_four]
      rw [h1, h2]
      have h3 : 0 < (Real.sqrt 2 : ℝ) := by positivity
      have h4 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by linarith)
      field_simp
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), h4, sq_nonneg (Real.sqrt 2 ^ 2 - 2)]
  · -- Show that 1 is a lower bound
    intro x hx
    rcases hx with ⟨α, hα, hx⟩
    have hα1 : 0 < α := hα.1
    have hα2 : α < π / 2 := hα.2
    have h1 : 0 < sin α := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hα1, Real.pi_gt_three]
      linarith [hα1, Real.pi_pos, hα2]
      all_goals nlinarith [Real.pi_gt_three]
    have h2 : 0 < cos α := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [hα1, Real.pi_pos, hα2]
      · linarith [hα1, Real.pi_pos, hα2]
    have h3 : (sin α) ^ 3 / cos α + (cos α) ^ 3 / sin α ≥ 1 := by
      have h4 : (sin α) ^ 2 + (cos α) ^ 2 = 1 := Real.sin_sq_add_cos_sq α
      have h5 : 0 < sin α * cos α := by nlinarith
      have h6 : (sin α) ^ 4 + (cos α) ^ 4 ≥ (sin α * cos α) := by
        nlinarith [sq_nonneg ( (sin α) ^ 2 - (cos α) ^ 2 ), sq_nonneg ( (sin α) - (cos α) ), sq_nonneg ( (sin α) * (cos α) - 1 / 2 ), sq_nonneg ( (sin α) - 1 / Real.sqrt 2 ), sq_nonneg ( (cos α) - 1 / Real.sqrt 2 ), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) >0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num: (0 : ℝ) ≤ (2 : ℝ) ) ]
      have h7 : (sin α) ^ 3 / cos α + (cos α) ^ 3 / sin α - 1 ≥ 0 := by
        have h8 : (sin α) ^ 3 / cos α + (cos α) ^ 3 / sin α - 1 = ( (sin α) ^ 4 + (cos α) ^ 4 - (sin α * cos α) ) / (sin α * cos α) := by
          field_simp
          <;> nlinarith [Real.sin_sq_add_cos_sq α]
        rw [h8]
        apply div_nonneg
        linarith [h6]
        nlinarith
      linarith
    linarith [hx, h3]