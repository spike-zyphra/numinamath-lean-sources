import Mathlib

open Real Set
open scoped Real

theorem inequalities_289683 (α : Real) (hα : α ∈ Ioo 0 (π / 2)) :
    sin α + cos α ≤ sqrt 2 ∧ (∃ α : Real, α ∈ Ioo 0 (π / 2) ∧ sin α + cos α = sqrt 2) := by
  have h1 : 0 < α := hα.1
  have h2 : α < π / 2 := hα.2
  have h3 : sin α + cos α ≤ sqrt 2 := by
    have h4 : (sin α + cos α) ^ 2 ≤ 2 := by
      have h5 : (sin α + cos α) ^ 2 = (sin α) ^ 2 + (cos α) ^ 2 + 2 * (sin α * cos α) := by 
        ring
      have h6 : (sin α) ^ 2 + (cos α) ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq α
      have h7 : 2 * (sin α * cos α) ≤ 1 := by 
        nlinarith [sq_nonneg (sin α - cos α), Real.sin_sq_add_cos_sq α]
      nlinarith [Real.sin_sq_add_cos_sq α, h7]
    have h8 : sin α + cos α ≥ 0 := by 
      have h9 : sin α > 0 := by 
        apply sin_pos_of_pos_of_lt_pi
        linarith [h1, h2, Real.pi_pos]
        linarith [h1, h2, Real.pi_pos]
      have h10 : cos α > 0 := by 
        apply cos_pos_of_mem_Ioo
        constructor
        linarith [h1, h2, Real.pi_pos]
        linarith [h1, h2, Real.pi_pos]
      linarith
    have h11 : (sin α + cos α) ≤ sqrt 2 := by 
      nlinarith [h4, Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by linarith), sq_nonneg (sin α + cos α - sqrt 2)]
    linarith
  have h9 : ∃ α : Real, α ∈ Ioo 0 (π / 2) ∧ sin α + cos α = sqrt 2 := by 
    use Real.pi / 4
    constructor 
    · -- Show that π/4 is in the open interval (0, π/2)
      constructor 
      · -- Show that 0 < π/4
        linarith [Real.pi_pos]
      · -- Show that π/4 < π/2
        linarith [Real.pi_pos]
    · -- Show that sin (π/4) + cos (π/4) = sqrt 2
      have h8 : sin (Real.pi / 4) = sqrt 2 / 2 := Real.sin_pi_div_four
      have h9 : cos (Real.pi / 4) = sqrt 2 / 2 := Real.cos_pi_div_four
      rw [h8, h9]
      ring
  constructor 
  · exact h3 
  · exact h9