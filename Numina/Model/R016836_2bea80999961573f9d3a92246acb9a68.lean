import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_214672 {x : Fin 2 → ℝ}
  (hx : ∀ i, x i ∈ Ioo 0 (π/2)) :
  (cos (x 0) + cos (x 1))/2 ≤ cos ((x 0 + x 1)/2) := by 
  have h1 : 0 < x 0 := by 
    have h1 := hx 0 
    exact h1.left 
  have h2 : x 0 < π / 2 := by 
    have h1 := hx 0 
    exact h1.right 
  have h3 : 0 < x 1 := by 
    have h1 := hx 1 
    exact h1.left 
  have h4 : x 1 < π / 2 := by 
    have h1 := hx 1 
    exact h1.right 
  have h5 : cos (x 0) + cos (x 1) = 2 * cos ((x 0 + x 1) / 2) * cos ((x 0 - x 1) / 2) := by 
    have h6 : cos (x 0) + cos (x 1) = 2 * cos ((x 0 + x 1) / 2) * cos ((x 0 - x 1) / 2) := by 
      rw [show (x 0 : ℝ) = ( (x 0 + x 1) / 2 + (x 0 - x 1) / 2 ) by ring] 
      rw [show (x 1 : ℝ) = ( (x 0 + x 1) / 2 - (x 0 - x 1) / 2 ) by ring] 
      rw [cos_add, cos_sub] 
      ring 
    linarith 
  have h6 : cos ((x 0 - x 1) / 2) ≤ 1 := by 
    have h7 : cos ((x 0 - x 1) / 2) ≤ 1 := by 
      apply cos_le_one 
    linarith 
  have h7 : cos (x 0) + cos (x 1) ≤ 2 * cos ((x 0 + x 1) / 2) := by 
    have h8 : cos (x 0) + cos (x 1) = 2 * cos ((x 0 + x 1) / 2) * cos ((x 0 - x 1) / 2) := h5 
    have h9 : cos ((x 0 - x 1) / 2) ≤ 1 := h6 
    have h11 : cos ((x 0 + x 1) / 2) ≥ 0 := by 
      apply cos_nonneg_of_neg_pi_div_two_le_of_le 
      all_goals 
        linarith [h1, h2, h3, h4, Real.pi_pos] 
    have h12 : 2 * cos ((x 0 + x 1) / 2) * cos ((x 0 - x 1) / 2) ≤ 2 * cos ((x 0 + x 1) / 2) := by 
      nlinarith [h9, h11] 
    linarith [h8, h12] 
  linarith [h7]