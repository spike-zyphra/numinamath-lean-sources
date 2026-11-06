import Mathlib

theorem algebra_305820 (x : ℝ) (hx : 2000 - x ≥ 0 ∧ x - 2000 ≥ 0) :
    Real.sqrt (2000 - x) + Real.sqrt (x - 2000) ≤ 4 := by 
  have h1 : 2000 - x = 0 := by
    linarith
  have h2 : Real.sqrt (2000 - x) = 0 := by
    rw [h1]
    norm_num
  have h4 : x - 2000 = 0 := by
    linarith [h1]
  have h3 : Real.sqrt (x - 2000) = 0 := by
    rw [h4]
    norm_num
  rw [h2, h3]
  all_goals norm_num