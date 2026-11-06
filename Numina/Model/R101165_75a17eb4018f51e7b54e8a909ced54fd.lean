import Mathlib

open Real Set
open scoped Real

theorem inequalities_121639 (α : Real) (hα : α ∈ Ioo 0 (π / 2)) :
    1 / 2 < sqrt 3 / 2 * sin α + 1 / 2 * cos α ∧
    sqrt 3 / 2 * sin α + 1 / 2 * cos α ≤ 1 := by 
  rcases hα with ⟨hα1, hα2⟩
  have h3 : sqrt 3 / 2 * sin α + 1 / 2 * cos α = sin (α + π / 6) := by
    rw [sin_add]
    have h4 : sin (π / 6) = 1 / 2 := sin_pi_div_six
    have h5 : cos (π / 6) = sqrt 3 / 2 := cos_pi_div_six
    rw [h4, h5]
    ring
  rw [h3]
  constructor
  · -- First inequality: 1 / 2 < sin (α + π / 6)
    by_cases h9 : α + π / 6 ≤ π / 2
    · -- Case 1 : α + π/6 ≤ π/2 
      have h10 : π / 6 < α + π / 6 := by 
        linarith [hα1]
      have h11 : sin (α + π / 6) > sin (π / 6) := by 
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals linarith 
      have h12 : sin (π / 6) = 1 / 2 := by 
        exact sin_pi_div_six 
      linarith 
    · -- Case 2 : α + π/6 > π/2 
      have h13 : π / 2 < α + π / 6 := by 
        linarith 
      have h14 : α + π / 6 < π := by 
        nlinarith [Real.pi_pos, hα2]
      have h15 : sin (α + π / 6) = sin (π - (α + π / 6)) := by 
        rw [Real.sin_pi_sub]
      have h16 : π - (α + π / 6) < π / 2 := by
        nlinarith [Real.pi_pos, hα2]
      have h17 : π - (α + π / 6) > π / 6 := by 
        nlinarith [Real.pi_pos, hα1]
      have h18 : sin (π - (α + π / 6)) > sin (π / 6) := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        all_goals nlinarith [Real.pi_pos]
      have h12 : sin (π / 6) = 1 / 2 := by 
        exact sin_pi_div_six 
      linarith [h15, h17, h12, h18]
  · -- Second inequality: sin (α + π / 6) ≤ 1
    have h4 : sin (α + π / 6) ≤ 1 := by
      apply sin_le_one 
    linarith