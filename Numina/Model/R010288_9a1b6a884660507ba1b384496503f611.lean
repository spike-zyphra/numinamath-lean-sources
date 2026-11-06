import Mathlib

theorem algebra_9415 : IsLeast {y | ∃ x : ℝ, y = abs (x - 2) + 3} 3 := by 
  constructor
  · -- First part, to show that 3 is in the set
    use 2
    norm_num [abs_zero]
    
  · -- Second part, to show that 3 is the least element
    intro y hy
    rcases hy with ⟨x, hx⟩

    have h_abs_nonneg : abs (x - 2) ≥ 0 := abs_nonneg (x - 2)
   
    linarith [h_abs_nonneg, hx]