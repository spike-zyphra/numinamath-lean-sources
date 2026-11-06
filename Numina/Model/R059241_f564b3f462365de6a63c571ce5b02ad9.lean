import Mathlib

theorem algebra_164495 : (Real.cos (68 * Real.pi / 180) * Real.cos (8 * Real.pi / 180) -
    Real.cos (82 * Real.pi / 180) * Real.cos (22 * Real.pi / 180)) /
    (Real.cos (53 * Real.pi / 180) * Real.cos (23 * Real.pi / 180) -
    Real.cos (67 * Real.pi / 180) * Real.cos (37 * Real.pi / 180)) = 1 := by

  have h1 : Real.cos (68 * Real.pi / 180) = Real.sin (22 * Real.pi / 180) := by
    have h1 : 68 * Real.pi / 180 = Real.pi / 2 - 22 * Real.pi / 180 := by
      ring
    rw [h1]
    rw [Real.cos_pi_div_two_sub]

  have h2 : Real.cos (82 * Real.pi / 180) = Real.sin (8 * Real.pi / 180) := by
    have h2 : 82 * Real.pi / 180 = Real.pi / 2 - 8 * Real.pi / 180 := by
      ring
    rw [h2]
    rw [Real.cos_pi_div_two_sub]

  have h3 : Real.cos (53 * Real.pi / 180) = Real.sin (37 * Real.pi / 180) := by
    have h3 : 53 * Real.pi / 180 = Real.pi / 2 - 37 * Real.pi / 180 := by
      ring
    rw [h3]
    rw [Real.cos_pi_div_two_sub]

  have h4 : Real.cos (67 * Real.pi / 180) = Real.sin (23 * Real.pi / 180) := by
    have h4 : 67 * Real.pi / 180 = Real.pi / 2 - 23 * Real.pi / 180 := by
      ring
    rw [h4]
    rw [Real.cos_pi_div_two_sub]

  have h5 : Real.cos (68 * Real.pi / 180) * Real.cos (8 * Real.pi / 180) -
      Real.cos (82 * Real.pi / 180) * Real.cos (22 * Real.pi / 180) =
      Real.sin (22 * Real.pi / 180) * Real.cos (8 * Real.pi / 180) - Real.sin (8 * Real.pi / 180) * Real.cos (22 * Real.pi / 180) := by
    rw [h1, h2]

  have h6 : Real.sin (22 * Real.pi / 180) * Real.cos (8 * Real.pi / 180) - Real.sin (8 * Real.pi / 180) * Real.cos (22 * Real.pi / 180) = Real.sin (22 * Real.pi / 180 - 8 * Real.pi / 180) := by
    rw [show 22 * Real.pi / 180 - 8 * Real.pi / 180 = (22 * Real.pi / 180) - (8 * Real.pi / 180) by ring]
    rw [Real.sin_sub]
    <;> ring

  have h7 : Real.cos (53 * Real.pi / 180) * Real.cos (23 * Real.pi / 180) - Real.cos (67 * Real.pi / 180) * Real.cos (37 * Real.pi / 180) =
      Real.sin (37 * Real.pi / 180) * Real.cos (23 * Real.pi / 180) - Real.sin (23 * Real.pi / 180) * Real.cos (37 * Real.pi / 180) := by
    rw [h3, h4]

  have h8 : Real.sin (37 * Real.pi / 180) * Real.cos (23 * Real.pi / 180) - Real.sin (23 * Real.pi / 180) * Real.cos (37 * Real.pi / 180) = Real.sin (37 * Real.pi / 180 - 23 * Real.pi / 180) := by
    rw [show 37 * Real.pi / 180 - 23 * Real.pi / 180 = (37 * Real.pi / 180) - (23 * Real.pi / 180) by ring]
    rw [Real.sin_sub]
    <;> ring

  have h9 : 22 * Real.pi / 180 - 8 * Real.pi / 180 = 14 * Real.pi / 180 := by
    linarith [Real.pi_pos]

  have h10 : 37 * Real.pi / 180 - 23 * Real.pi / 180 = 14 * Real.pi / 180 := by
    linarith [Real.pi_pos]

  have h11 : Real.sin (22 * Real.pi / 180 - 8 * Real.pi / 180) = Real.sin (14 * Real.pi / 180) := by
    rw [h9]

  have h12 : Real.sin (37 * Real.pi / 180 - 23 * Real.pi / 180) = Real.sin (14 * Real.pi / 180) := by
    rw [h10]

  have num_eq : Real.cos (68 * Real.pi / 180) * Real.cos (8 * Real.pi / 180) - Real.cos (82 * Real.pi / 180) * Real.cos (22 * Real.pi / 180) = Real.sin (14 * Real.pi / 180) := by
    rw [h5, h6, h11]

  have den_eq : Real.cos (53 * Real.pi / 180) * Real.cos (23 * Real.pi / 180) - Real.cos (67 * Real.pi / 180) * Real.cos (37 * Real.pi / 180) = Real.sin (14 * Real.pi / 180) := by
    rw [h7, h8, h12]

  rw [num_eq, den_eq]

  have h13 : Real.sin (14 * Real.pi / 180) ≠ 0 := by
    have h14 : 0 < (14 * Real.pi / 180) := by
      have hpi : 0 < Real.pi := Real.pi_pos
      linarith [hpi]
    have h15 : Real.sin (14 * Real.pi / 180) > 0 := by
      apply Real.sin_pos_of_pos_of_lt_pi
      . linarith [Real.pi_pos]
      . 
        have h2 : 14 * Real.pi / 180 < Real.pi := by
          linarith [Real.pi_gt_314]
        linarith [Real.pi_pos, Real.pi_gt_314]
    linarith [h15]

  field_simp [h13]