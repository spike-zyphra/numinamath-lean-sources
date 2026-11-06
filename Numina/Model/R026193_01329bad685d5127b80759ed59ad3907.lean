import Mathlib

open Real Set
open scoped Real

theorem calculus_22964 : tan (π/18) * tan (2*π/18) * tan (3*π/18) * tan (4*π/18) * tan (5*π/18) * tan (6*π/18) * tan (7*π/18) * tan (8*π/18) = 1 := by

  have h1 : tan (3 * π / 18) * tan (6 * π / 18) = 1 := by
    have h2 : 3 * π / 18 = π / 6 := by ring
    have h3 : 6 * π / 18 = π / 3 := by ring
    rw [h2, h3]
    have h4 : tan (π / 6) = 1 / Real.sqrt 3 := by
      rw [tan_pi_div_six]
    have h5 : tan (π / 3) = Real.sqrt 3 := by
      rw [tan_pi_div_three]
    rw [h4, h5]
    field_simp

  have h2 : tan (π / 18) * tan (8 * π / 18) = 1 := by
    have h3 : 8 * π / 18 = π / 2 - π / 18 := by
      linarith [Real.pi_pos]
    rw [h3]
    have h4 : tan (π / 2 - π / 18) = Real.cos (π / 18) / Real.sin (π / 18) := by
      have h5 : tan (π / 2 - π / 18) = Real.sin (π / 2 - π / 18) / Real.cos (π / 2 - π / 18) := by
        rw [Real.tan_eq_sin_div_cos]
      rw [h5]
      have h6 : Real.sin (π / 2 - π / 18) = Real.cos (π / 18) := by
        rw [Real.sin_pi_div_two_sub]
      have h7 : Real.cos (π / 2 - π / 18) = Real.sin (π / 18) := by
        rw [Real.cos_pi_div_two_sub]
      rw [h6, h7]

    have h8 : tan (π / 18) = Real.sin (π / 18) / Real.cos (π / 18) := by
      rw [Real.tan_eq_sin_div_cos]
    rw [h8, h4]
    have h9 : Real.sin (π / 18) ≠ 0 := by
      have h9 : Real.sin (π / 18) > 0 := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      linarith
    have h10 : Real.cos (π / 18) ≠ 0 := by
      have h12 : Real.cos (π / 18) > 0 := by
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      linarith
    field_simp [h9, h10]

  have h3 : tan (2 * π / 18) * tan (7 * π / 18) = 1 := by
    have h4 : 7 * π / 18 = π / 2 - 2 * π / 18 := by
      linarith [Real.pi_pos]
    rw [h4]
    have h5 : tan (π / 2 - 2 * π / 18) = Real.cos (2 * π / 18) / Real.sin (2 * π / 18) := by
      have h6 : tan (π / 2 - 2 * π / 18) = Real.sin (π / 2 - 2 * π / 18) / Real.cos (π / 2 - 2 * π / 18) := by
        rw [Real.tan_eq_sin_div_cos]
      rw [h6]
      have h7 : Real.sin (π / 2 - 2 * π / 18) = Real.cos (2 * π / 18) := by
        rw [Real.sin_pi_div_two_sub]
      have h8 : Real.cos (π / 2 - 2 * π / 18) = Real.sin (2 * π / 18) := by
        rw [Real.cos_pi_div_two_sub]
      rw [h7, h8]

    have h9 : tan (2 * π / 18) = Real.sin (2 * π / 18) / Real.cos (2 * π / 18) := by
      rw [Real.tan_eq_sin_div_cos]
    rw [h9, h5]
    have h10 : Real.sin (2 * π / 18) ≠ 0 := by
      have h9 : Real.sin (2 * π / 18) > 0 := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      linarith
    have h11 : Real.cos (2 * π / 18) ≠ 0 := by
      have h12 : Real.cos (2 * π / 18) > 0 := by
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      linarith
    field_simp [h10, h11]

  have h4 : tan (4 * π / 18) * tan (5 * π / 18) = 1 := by
    have h5 : 5 * π / 18 = π / 2 - 4 * π / 18 := by
      linarith [Real.pi_pos]
    rw [h5]
    have h6 : tan (π / 2 - 4 * π / 18) = Real.cos (4 * π / 18) / Real.sin (4 * π / 18) := by
      have h7 : tan (π / 2 - 4 * π / 18) = Real.sin (π / 2 - 4 * π / 18) / Real.cos (π / 2 - 4 * π / 18) := by
        rw [Real.tan_eq_sin_div_cos]
      rw [h7]
      have h8 : Real.sin (π / 2 - 4 * π / 18) = Real.cos (4 * π / 18) := by
        rw [Real.sin_pi_div_two_sub]
      have h9 : Real.cos (π / 2 - 4 * π / 18) = Real.sin (4 * π / 18) := by
        rw [Real.cos_pi_div_two_sub]
      rw [h8, h9]

    have h10 : tan (4 * π / 18) = Real.sin (4 * π / 18) / Real.cos (4 * π / 18) := by
      rw [Real.tan_eq_sin_div_cos]
    rw [h10, h6]
    have h11 : Real.sin (4 * π / 18) ≠ 0 := by
      have h12 : Real.sin (4 * π / 18) > 0 := by
        apply Real.sin_pos_of_pos_of_lt_pi
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      linarith
    have h12 : Real.cos (4 * π / 18) ≠ 0 := by
      have h13 : Real.cos (4 * π / 18) > 0 := by
        apply Real.cos_pos_of_mem_Ioo
        constructor
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      linarith
    field_simp [h11, h12]

  calc
    tan (π/18) * tan (2*π/18) * tan (3*π/18) * tan (4*π/18) * tan (5*π/18) * tan (6*π/18) * tan (7*π/18) * tan (8*π/18)
      = (tan (π/18) * tan (8*π/18)) * (tan (2*π/18) * tan (7*π/18)) * (tan (4*π/18) * tan (5*π/18)) * (tan (3*π/18) * tan (6*π/18)) := by 
        ring
    _ = 1 * 1 * 1 * 1 := by 
      rw [h2, h3, h4, h1]
    _ = 1 := by 
      norm_num