import Mathlib

theorem algebra_227930 : (2 * Real.cos (40 * Real.pi / 180) - Real.cos (20 * Real.pi / 180)) / Real.sin (20 * Real.pi / 180) = Real.sqrt 3 := by
  have h1 : 40 * Real.pi / 180 = Real.pi / 3 - 20 * Real.pi / 180 := by 
    linarith [Real.pi_pos]
  have h2 : Real.cos (40 * Real.pi / 180) = Real.cos (Real.pi / 3) * Real.cos (20 * Real.pi / 180) + Real.sin (Real.pi / 3) * Real.sin (20 * Real.pi / 180) := by
    rw [h1]
    rw [Real.cos_sub]
  have h3 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have h4 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have eq1 : Real.cos (40 * Real.pi / 180) = 1 / 2 * Real.cos (20 * Real.pi / 180) + Real.sqrt 3 / 2 * Real.sin (20 * Real.pi / 180) := by
    rw [h2, h3, h4]
    all_goals ring_nf
  have eq2 : 2 * Real.cos (40 * Real.pi / 180) = Real.cos (20 * Real.pi / 180) + Real.sqrt 3 * Real.sin (20 * Real.pi / 180) := by
    rw [eq1]
    ring_nf
  have eq3 : 2 * Real.cos (40 * Real.pi / 180) - Real.cos (20 * Real.pi / 180) = Real.sqrt 3 * Real.sin (20 * Real.pi / 180) := by 
    linarith [eq2]
  have h5 : Real.sin (20 * Real.pi / 180) > 0 := by 
    apply Real.sin_pos_of_pos_of_lt_pi
    · -- Show 0 < 20 * Real.pi / 180
      linarith [Real.pi_pos]
    · -- Show 20 * Real.pi / 180 < Real.pi
      linarith [Real.pi_pos]
  rw [eq3]
  field_simp [h5]
  all_goals nlinarith