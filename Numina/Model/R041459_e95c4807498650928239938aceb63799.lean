import Mathlib

open Real Set
open scoped Real

theorem other_43630 : (4 * (cos (9 * π / 180))^2 - 3) * (4 * (cos (27 * π / 180))^2 - 3) = tan (9 * π / 180) := by
  have h1 : 4 * (cos (9 * π / 180))^2 - 3 = cos (27 * π / 180) / cos (9 * π / 180) := by
    have h2 : cos (27 * π / 180) = 4 * (cos (9 * π / 180))^3 - 3 * cos (9 * π / 180) := by
      have h3 : 27 * π / 180 = 3 * (9 * π / 180) := by ring
      rw [h3]
      have h4 : cos (3 * (9 * π / 180)) = 4 * (cos (9 * π / 180))^3 - 3 * cos (9 * π / 180) := by
        rw [cos_three_mul]
      exact h4
    rw [h2]
    field_simp [show cos (9 * π / 180) ≠ 0 by
      have h11 : cos (9 * π / 180) > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        · nlinarith [show 0 < 9 * π / 180 by nlinarith [Real.pi_pos]]
        · nlinarith [show 9 * π / 180 < π / 2 by nlinarith [Real.pi_pos]]
      linarith
    ]
    <;> nlinarith
  have h2 : 4 * (cos (27 * π / 180))^2 - 3 = cos (81 * π / 180) / cos (27 * π / 180) := by
    have h3 : cos (81 * π / 180) = 4 * (cos (27 * π / 180))^3 - 3 * cos (27 * π / 180) := by
      have h4 : 81 * π / 180 = 3 * (27 * π / 180) := by ring
      rw [h4]
      have h5 : cos (3 * (27 * π / 180)) = 4 * (cos (27 * π / 180))^3 - 3 * cos (27 * π / 180) := by
        rw [cos_three_mul]
      exact h5
    rw [h3]
    field_simp [show cos (27 * π / 180) ≠ 0 by
      have h11 : cos (27 * π / 180) > 0 := by
        apply cos_pos_of_mem_Ioo
        constructor
        · nlinarith [show 0 < 27 * π / 180 by nlinarith [Real.pi_pos]]
        · nlinarith [show 27 * π / 180 < π / 2 by nlinarith [Real.pi_pos]]
      linarith
    ]
    <;> nlinarith
  rw [h1, h2]
  have h3 : cos (81 * π / 180) = sin (9 * π / 180) := by
    have h4 : 81 * π / 180 = π / 2 - (9 * π / 180) := by ring
    rw [h4]
    rw [cos_pi_div_two_sub]
  have h5 : cos (27 * π / 180) ≠ 0 := by
    have h11 : cos (27 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · nlinarith [show 0 < 27 * π / 180 by nlinarith [Real.pi_pos]]
      · nlinarith [show 27 * π / 180 < π / 2 by nlinarith [Real.pi_pos]]
    linarith
  have h6 : cos (9 * π / 180) ≠ 0 := by
    have h11 : cos (9 * π / 180) > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · nlinarith [show 0 < 9 * π / 180 by nlinarith [Real.pi_pos]]
      · nlinarith [show 9 * π / 180 < π / 2 by nlinarith [Real.pi_pos]]
    linarith
  have ht : cos (27 * π / 180) / cos (9 * π / 180) * (cos (81 * π / 180) / cos (27 * π / 180)) = cos (81 * π / 180) / cos (9 * π / 180) := by
    field_simp [h6, h5]
    <;> nlinarith
  rw [ht]
  rw [h3]
  have h7 : tan (9 * π / 180) = sin (9 * π / 180) / cos (9 * π / 180) := by
    rw [tan_eq_sin_div_cos]
  rw [h7]
  all_goals
    all_goals
      field_simp [show cos (9 * π / 180) ≠ 0 by
        have h11 : cos (9 * π / 180) > 0 := by
          apply cos_pos_of_mem_Ioo
          constructor
          · nlinarith [show 0 < 9 * π / 180 by nlinarith [Real.pi_pos]]
          · nlinarith [show 9 * π / 180 < π / 2 by nlinarith [Real.pi_pos]]
        linarith
      ]
      <;> nlinarith