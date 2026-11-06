import Mathlib

open Real

theorem algebra_186175 : tan (435 * π / 180) + tan (375 * π / 180) = 4 := by
  have h1 : tan (435 * π / 180) = tan (5 * π / 12) := by
    have h1' : 435 * π / 180 = 5 * π / 12 + π + π := by 
      linarith [Real.pi_pos]
    rw [h1']
    simp [tan_add_pi]
  have h2 : tan (375 * π / 180) = tan (π / 12) := by 
    have h2' : 375 * π / 180 = π / 12 + π + π := by 
      linarith [Real.pi_pos]
    rw [h2']
    simp [tan_add_pi]
  rw [h1, h2]
  have h3 : 5 * π / 12 = Real.pi / 2 - π / 12 := by 
    linarith [Real.pi_pos]
  have h4 : sin (π / 6) = 1 / 2 := sin_pi_div_six
  have h5 : sin (π / 6) = 2 * sin (π / 12) * cos (π / 12) := by 
    rw [← sin_two_mul]
    ring_nf
    <;> try linarith [Real.pi_pos]
  rw [h5] at h4
  have h7 : tan (5 * π / 12) = 1 / tan (π / 12) := by 
    rw [show tan (5 * π / 12) = tan (Real.pi / 2 - π / 12) by rw [h3]]
    have h12 : Real.pi / 2 - π / 12 ≠ Real.pi / 2 := by 
      linarith [Real.pi_pos]
    rw [tan_pi_div_two_sub]
    all_goals try linarith [Real.pi_pos]
    all_goals try simp [show π / 12 > 0 by positivity]
    <;> try linarith [Real.sin_pos_of_pos_of_lt_pi (show π / 12 > 0 by positivity) (show π / 12 < Real.pi by linarith [Real.pi_pos])]

  have h7' : tan (5 * π / 12) + tan (π / 12) = 4 := by 
    rw [h7]
    -- Show that 1 / tan (π / 12) + tan (π / 12) = 4
    -- which is (1 + tan^2(π/12)) / tan(π/12) = 4
    have h8 : sin (π / 12) * cos (π / 12) = 1 / 4 := by 
      nlinarith [Real.sin_sq_add_cos_sq (π / 12), h4]
    have h9 : Real.sin (π / 12) > 0 := by 
      apply sin_pos_of_pos_of_lt_pi
      linarith [Real.pi_pos]
      linarith [Real.pi_pos]
    have h10 : Real.cos (π / 12) > 0 := by 
      apply cos_pos_of_mem_Ioo
      constructor <;> linarith [Real.pi_pos]
    have h11 : tan (π / 12) > 0 := by 
      apply tan_pos_of_pos_of_lt_pi_div_two
      linarith [Real.pi_pos]
      all_goals linarith [Real.pi_pos]
    have h12 : (tan (π / 12)) ≠ 0 := by positivity
    have h13 : (1 / tan (π / 12) + tan (π / 12)) = 4 := by
      have h21 : tan (π / 12) = Real.sin (π / 12) / Real.cos (π / 12) := by 
        rw [Real.tan_eq_sin_div_cos]
      rw [h21]
      have : Real.cos (π / 12) ≠ 0 := by linarith [Real.cos_pos_of_mem_Ioo (show π / 12 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by 
        constructor <;> linarith [Real.pi_pos]
      )]
      field_simp
      nlinarith [Real.sin_sq_add_cos_sq (π / 12), h8]
    linarith [h13]
  linarith [h7']