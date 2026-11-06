import Mathlib

open Real Set
open scoped Real

theorem algebra_163246 (α : ℝ) (hα : α ∈ Ioc 0 π) :
    sqrt (1 + sin (α / 2)) - sqrt (1 - sin (α / 2)) = 2 * sin (α / 4) := by
  rcases hα with ⟨hα1, hα2⟩
  have h1 : 0 < α := hα1
  have h2 : α ≤ π := hα2
  have h3 : 0 < α / 4 := by linarith
  have h4 : α / 4 ≤ π / 4 := by linarith [h2]
  have h5 : sin (α / 4) > 0 := by 
    apply sin_pos_of_pos_of_lt_pi
    linarith
    linarith
  have h6 : cos (α / 4) > 0 := by 
    apply cos_pos_of_mem_Ioo
    constructor
    linarith
    linarith
  have h7 : cos (α / 4) ≥ sin (α / 4) := by
    have h8 : sin (π / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have h9 : cos (π / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h10 : sin (α / 4) ≤ sin (π / 4) := by
      apply sin_le_sin_of_le_of_le_pi_div_two
      all_goals linarith
    have h11 : cos (α / 4) = sin (π / 2 - (α / 4)) := by
      rw [← sin_pi_div_two_sub]
    have h12 : π / 2 - (α / 4) ≥ α / 4 := by 
      linarith [show α / 4 ≤ π / 4 by linarith]
    have h13 : sin (π / 2 - (α / 4)) ≥ sin (α / 4) := by 
      apply sin_le_sin_of_le_of_le_pi_div_two
      all_goals linarith
    linarith [h10, h13, h11]
  
  have h8 : sqrt (1 + sin (α / 2)) = sin (α / 4) + cos (α / 4) := by
    have h9 : (sin (α / 4) + cos (α / 4)) ^ 2 = 1 + sin (α / 2) := by
      have h10 : (sin (α / 4) + cos (α / 4)) ^ 2 = sin (α / 4) ^ 2 + cos (α / 4) ^ 2 + 2 * (sin (α / 4) * cos (α / 4)) := by ring
      rw [h10]
      have h11 : sin (α / 4) ^ 2 + cos (α / 4) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq (α / 4)
      have h12 : 2 * (sin (α / 4) * cos (α / 4)) = sin (α / 2) := by 
        have h13 : sin (α / 2) = 2 * sin (α / 4) * cos (α / 4) := by 
          rw [←sin_two_mul (α / 4)]
          ring_nf
        linarith [h13]
      linarith [h11, h12]
    have h14 : 0 ≤ sin (α / 4) + cos (α / 4) := by 
      linarith [h5, h6]
    rw [← h9]
    field_simp [h14]

  have h15 : sqrt (1 - sin (α / 2)) = cos (α / 4) - sin (α / 4) := by
    have h16 : (cos (α / 4) - sin (α / 4)) ^ 2 = 1 - sin (α / 2) := by 
      have h17 : (cos (α / 4) - sin (α / 4)) ^ 2 = cos (α / 4) ^ 2 + sin (α / 4) ^ 2 - 2 * (sin (α / 4) * cos (α / 4)) := by ring
      rw [h17]
      have h18 : cos (α / 4) ^ 2 + sin (α / 4) ^ 2 = 1 := by
        linarith [Real.sin_sq_add_cos_sq (α / 4)]
      have h19 : 2 * (sin (α / 4) * cos (α / 4)) = sin (α / 2) := by 
        have h20 : sin (α / 2) = 2 * sin (α / 4) * cos (α / 4) := by 
          rw [←sin_two_mul (α / 4)]
          ring_nf
        linarith [h20]
      linarith [h18, h19]
    have h21 : 0 ≤ cos (α / 4) - sin (α / 4) := by 
      linarith [h7, h5, h6]
    rw [← h16]
    field_simp [h21]

  rw [h8, h15]
  linarith