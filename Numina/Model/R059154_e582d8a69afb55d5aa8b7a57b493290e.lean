import Mathlib

open Real

theorem algebra_4156 : Real.sin (71 * Real.pi / 180) - Real.cos (79 * Real.pi / 180) = Real.cos (41 * Real.pi / 180) := by
  have h2 : Real.cos (79 * Real.pi / 180) = Real.sin (11 * Real.pi / 180) := by
    have h21 : 79 * Real.pi / 180 = Real.pi / 2 - 11 * Real.pi / 180 := by
      linarith [Real.pi_pos]
    rw [h21]
    rw [Real.cos_pi_div_two_sub]
  rw [h2]
  have h3 : Real.sin (71 * Real.pi / 180) - Real.sin (11 * Real.pi / 180) = 
          2 * Real.cos (41 * Real.pi / 180) * Real.sin (30 * Real.pi / 180) := by
    have h5 : Real.sin (71 * Real.pi / 180) - Real.sin (11 * Real.pi / 180) =
          2 * Real.cos (41 * Real.pi / 180) * Real.sin (30 * Real.pi / 180) := by
      have h51 : Real.sin (71 * Real.pi / 180) - Real.sin (11 * Real.pi / 180) =
          2 * Real.cos ( (71 * Real.pi / 180 + 11 * Real.pi / 180) / 2 ) *
          Real.sin ( (71 * Real.pi / 180 - 11 * Real.pi / 180) / 2 ) := by 
        rw [Real.sin_sub_sin]
        all_goals ring_nf
        <;> try linarith
      have h52 : (71 * Real.pi / 180 + 11 * Real.pi / 180) / 2 = 41 * Real.pi / 180 := by
        linarith
      have h53 : (71 * Real.pi / 180 - 11 * Real.pi / 180) / 2 = 30 * Real.pi / 180 := by
        linarith
      rw [h52, h53] at h51
      linarith
    linarith
  rw [h3]
  have h4 : Real.sin (30 * Real.pi / 180) = 1 / 2 := by
    have h51 : 30 * Real.pi / 180 = Real.pi / 6 := by
      linarith [Real.pi_pos]
    rw [h51]
    rw [Real.sin_pi_div_six]
    all_goals linarith
  rw [h4]
  all_goals linarith
  <;> try linarith