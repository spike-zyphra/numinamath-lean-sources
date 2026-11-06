import Mathlib

theorem algebra_229942 :
    {x : ℝ | x > 0 ∧ x < 4 ∧ 
    20 * x + 30 * (x - 1) + 40 * (x - 2) + 50 * (x - 3) + 60 * (x - 4) = 0} = 
    {2.5} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x in the left side, need to prove in the right
    rintro ⟨hx1, hx2, heq⟩ 
    have h_eq : x = 2.5 := by
      linarith
    linarith [h_eq]
  · -- Assume x in the right side, need to prove in the left 
    intro h_eq 
    have h1 : x > 0 := by 
      rw [show x = (2.5 : ℝ) by linarith [h_eq]]
      norm_num 
    have h2 : x < 4 := by 
      rw [show x = (2.5 : ℝ) by linarith [h_eq]]
      norm_num 
    have h3 : 20 * x + 30 * (x - 1) + 40 * (x - 2) + 50 * (x - 3) + 60 * (x - 4) = 0 := by 
      rw [show x = (2.5 : ℝ) by linarith [h_eq]]
      norm_num 
    exact ⟨h1, h2, h3⟩ 
  all_goals norm_num 
  all_goals linarith