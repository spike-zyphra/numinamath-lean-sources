import Mathlib

open Real Set
open scoped Real

theorem algebra_292666 :
    IsLeast {x | ∃ α : ℝ, α ∈ Ioo 0 (π/2) ∧ x = sin α ^ 3 / cos α + cos α ^ 3 / sin α} 1 := by 
  constructor 
  · -- Show 1 is in the set.
    use Real.pi / 4
    constructor
    · -- Show π/4 is in the open interval (0, π/2)
      have h1 : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
      have h2 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
      exact ⟨h1, h2⟩
    · -- Show at π/4, the value is 1.
      have h3 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      have h4 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      rw [h3, h4]
      have h5 : (Real.sqrt 2 / 2 : ℝ) ^ 3 / (Real.sqrt 2 / 2) = 1 / 2 := by
        field_simp
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by linarith)]
      linarith [h5]
  · -- Show for all x in the set, 1 ≤ x
    intro x hx
    rcases hx with ⟨α, hα, hx⟩
    rcases hα with ⟨h1, h2⟩
    have h3 : 0 < sin α := by 
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos, h1, h2]
      linarith [Real.pi_pos, h1, h2]
    have h4 : 0 < cos α := by 
      apply cos_pos_of_mem_Ioo
      constructor
      linarith [Real.pi_pos, h1, h2]
      linarith [Real.pi_pos, h1, h2]
    have h5 : sin α ^ 3 / cos α + cos α ^ 3 / sin α ≥ 1 := by
      have h6 : sin α ^ 4 + cos α ^ 4 ≥ sin α * cos α := by
        nlinarith [sq_nonneg (sin α ^ 2 - cos α ^ 2), sq_nonneg (sin α - cos α), sq_pos_of_pos h3, sq_pos_of_pos h4, Real.sin_sq_add_cos_sq α, sq_nonneg (sin α * cos α), mul_pos h3 h4]
      have h7 : sin α * cos α > 0 := by nlinarith
      have h8 : sin α ^ 3 / cos α + cos α ^ 3 / sin α - 1 ≥ 0 := by
        have h9 : sin α ^ 3 / cos α + cos α ^ 3 / sin α - 1 =
          (sin α ^ 4 + cos α ^ 4 - sin α * cos α) / (sin α * cos α) := by 
          field_simp [show cos α ≠ 0 by linarith, show sin α ≠ 0 by linarith]
          ring
        rw [h9]
        have h10 : (sin α ^ 4 + cos α ^ 4 - sin α * cos α) / (sin α * cos α) ≥ 0 := by
          apply div_nonneg 
          linarith [h6, mul_pos h3 h4]
          all_goals nlinarith
        linarith 
      linarith 
    linarith [h5, hx]