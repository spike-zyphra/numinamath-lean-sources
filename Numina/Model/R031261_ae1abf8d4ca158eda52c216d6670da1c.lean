import Mathlib

open Real

theorem algebra_81812 : (sin (10 * π / 180) + sin (20 * π / 180)) / (cos (10 * π / 180) + cos (20 * π / 180)) = tan (15 * π / 180) := by
  have eq1 : sin (10 * π / 180) + sin (20 * π / 180) = 2 * sin (15 * π / 180) * cos (5 * π / 180) := by
    rw [show 10 * π / 180 = 15 * π / 180 - 5 * π / 180 by ring]
    rw [show 20 * π / 180 = 15 * π / 180 + 5 * π / 180 by ring]
    rw [sin_add, sin_sub]
    ring
  have eq2 : cos (10 * π / 180) + cos (20 * π / 180) = 2 * cos (15 * π / 180) * cos (5 * π / 180) := by
    rw [show 10 * π / 180 = 15 * π / 180 - 5 * π / 180 by ring]
    rw [show 20 * π / 180 = 15 * π / 180 + 5 * π / 180 by ring]
    rw [cos_add, cos_sub]
    ring
  have htan : tan (15 * π / 180) = sin (15 * π / 180) / cos (15 * π / 180) := by
    rw [tan_eq_sin_div_cos]
  rw [htan]
  rw [show (sin (10 * π / 180) + sin (20 * π / 180)) / (cos (10 * π / 180) + cos (20 * π / 180)) = (2 * sin (15 * π / 180) * cos (5 * π / 180)) / (2 * cos (15 * π / 180) * cos (5 * π / 180)) by rw [eq1, eq2]]

  have hcos1 : cos (15 * π / 180) ≠ 0 := by
    have h1 : 0 < 15 * π / 180 := by 
      nlinarith [Real.pi_pos]
    have h2 : cos (15 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    linarith
  have hcos2 : cos (5 * π / 180) ≠ 0 := by
    have h3 : 0 < 5 * π / 180 := by 
      nlinarith [Real.pi_pos]
    have h4 : cos (5 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
    linarith
  field_simp [hcos1, hcos2]
  <;> ring