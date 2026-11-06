import Mathlib

open Real

theorem algebra_117832 {x : ℝ} (hx : 0 < x ∧ x ≠ 1) :
    logb 3 x * logb x 5 = logb 3 5 ↔ True := by
  constructor
  · -- Show if equation then True
    intro h
    trivial 
  · -- Show if True then equation
    intro h 
    have h1 : logb 3 x * logb x 5 = logb 3 5 := by 
      have h2 : logb 3 x = log x / log (3 : ℝ) := by 
        field_simp [logb]
      have h3 : logb x 5 = log (5 : ℝ) / log x := by 
        field_simp [logb]
      have h4 : logb 3 5 = log (5 : ℝ) / log (3 : ℝ) := by 
        field_simp [logb]
      have h5 : log (3 : ℝ) ≠ 0 := by 
        have hx5 : log (3 : ℝ) > 0 := by 
          apply log_pos
          all_goals norm_num 
        linarith [hx5]
      have h6 : log x ≠ 0 := by 
        apply log_ne_zero_of_pos_of_ne_one
        exact hx.1
        exact hx.2
      rw [h2, h3, h4]
      field_simp [h5, h6]
      <;> nlinarith 
    tauto