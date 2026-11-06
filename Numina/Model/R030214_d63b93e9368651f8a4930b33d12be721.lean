import Mathlib

open Real

theorem algebra_161582 (α : ℝ) :
    (sin (3 * π - 4 * α) ^ 2 + 4 * cos ((3 / 2) * π - 2 * α) ^ 2 - 4) /
    (cos (π / 2 - 4 * α) ^ 2 - 4 * cos (2 * α - (5 / 2) * π) ^ 2) =
    1 / tan (2 * α) ^ 4 := by

  have h1 : Real.sin (3 * Real.pi - 4 * α) ^ 2 + 4 * Real.cos ((3 / 2) * Real.pi - 2 * α) ^ 2 - 4 =
      -4 * (Real.cos (2 * α)) ^ 4 := by
    have h1 : Real.sin (3 * Real.pi - 4 * α) = Real.sin (4 * α) := by
      have h2 : Real.sin (3 * Real.pi - 4 * α) = Real.sin (4 * α) := by
        have h3 : 3 * Real.pi - 4 * α = Real.pi - (4 * α) + 2 * Real.pi := by ring
        rw [h3]
        have h4 : Real.sin (Real.pi - (4 * α) + 2 * Real.pi) = Real.sin (Real.pi - (4 * α)) := by
          rw [Real.sin_add_two_pi]
        rw [h4]
        rw [Real.sin_pi_sub]
      exact h2
    have h2 : Real.cos ((3 / 2) * Real.pi - 2 * α) = - Real.sin (2 * α) := by
      have h5 : Real.cos ((3 / 2) * Real.pi - 2 * α) = - Real.sin (2 * α) := by
        have h5 : Real.cos ((3 / 2) * Real.pi - 2 * α) = Real.cos (3 * Real.pi / 2 - 2 * α) := by ring
        rw [h5]
        have h6 : Real.cos (3 * Real.pi / 2 - 2 * α) = - Real.sin (2 * α) := by
          have h5 : Real.cos (3 * Real.pi / 2 - 2 * α) = Real.cos (3 * Real.pi / 2) * Real.cos (2 * α) + Real.sin (3 * Real.pi / 2) * Real.sin (2 * α) := by
            rw [Real.cos_sub]
          have h6 : Real.cos (3 * Real.pi / 2) = 0 := by
            have h7 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
            rw [h7]
            have h8 : Real.cos (Real.pi + Real.pi / 2) = - Real.cos (Real.pi / 2) := by
              rw [Real.cos_add]
              simp [Real.cos_pi, Real.sin_pi]
            rw [h8]
            have h9 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
            rw [h9]
            all_goals norm_num
          have h7 : Real.sin (3 * Real.pi / 2) = -1 := by
            have h8 : 3 * Real.pi / 2 = Real.pi + Real.pi / 2 := by ring
            rw [h8]
            have h9 : Real.sin (Real.pi + Real.pi / 2) = - Real.sin (Real.pi / 2) := by
              rw [Real.sin_add]
              simp [Real.cos_pi, Real.sin_pi]
            rw [h9]
            have h10 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
            rw [h10]
            all_goals norm_num
          rw [h5, h6, h7]
          all_goals ring
        exact h6
      exact h5
    rw [h1, h2]
    have h3 : Real.sin (4 * α) ^ 2 = 4 * (Real.sin (2 * α) ^ 2) * (Real.cos (2 * α) ^ 2) := by
      have h4 : Real.sin (4 * α) = 2 * Real.sin (2 * α) * Real.cos (2 * α) := by
        rw [show 4 * α = 2 * (2 * α) by ring]
        rw [Real.sin_two_mul]
      rw [h4]
      all_goals ring
    rw [h3]
    have h4 : Real.sin (2 * α) ^ 2 + Real.cos (2 * α) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (2 * α)
    nlinarith [sq_nonneg (Real.sin (2 * α) ^ 2 - 1), sq_nonneg (Real.cos (2 * α) ^ 2 - 1), sq_nonneg (Real.sin (2 * α) ^ 2 - Real.cos (2 * α) ^ 2), sq_nonneg (Real.sin (2 * α) * Real.cos (2 * α)), sq_nonneg (Real.sin (2 * α) - 0), sq_nonneg (Real.cos (2 * α) - 0), Real.sin_sq_add_cos_sq (2 * α)]

  have h2 : cos (π / 2 - 4 * α) ^ 2 - 4 * cos (2 * α - (5 / 2) * π) ^ 2 = -4 * (Real.sin (2 * α)) ^ 4 := by
    have h3 : Real.cos (Real.pi / 2 - 4 * α) = Real.sin (4 * α) := by
      have h4 : Real.cos (Real.pi / 2 - 4 * α) = Real.sin (4 * α) := by
        rw [Real.cos_pi_div_two_sub]
      exact h4
    have h4 : Real.cos (2 * α - (5 / 2) * Real.pi) = Real.sin (2 * α) := by
      have h5 : 2 * α - (5 / 2) * Real.pi = 2 * α - (2 * Real.pi + Real.pi / 2) := by ring
      rw [h5]
      have h8 : Real.cos (2 * α - (2 * Real.pi + Real.pi / 2)) = Real.cos (2 * α - Real.pi / 2) := by
        have h9 : Real.cos (2 * α - (2 * Real.pi + Real.pi / 2)) = Real.cos (2 * α - Real.pi / 2 - 2 * Real.pi) := by ring
        rw [h9]
        have h10 : Real.cos (2 * α - Real.pi / 2 - 2 * Real.pi) = Real.cos (2 * α - Real.pi / 2) := by
          rw [Real.cos_sub_two_pi]
        exact h10
      rw [h8]
      have h11 : Real.cos (2 * α - Real.pi / 2) = Real.sin (2 * α) := by
        have h12 : Real.cos (2 * α - Real.pi / 2) = Real.sin (2 * α) := by
          rw [Real.cos_sub_pi_div_two]
        exact h12
      exact h11
    rw [h3, h4]
    have h5 : Real.sin (4 * α) ^ 2 = 4 * (Real.sin (2 * α) ^ 2) * (Real.cos (2 * α) ^ 2) := by
      have h4 : Real.sin (4 * α) = 2 * Real.sin (2 * α) * Real.cos (2 * α) := by
        rw [show 4 * α = 2 * (2 * α) by ring]
        rw [Real.sin_two_mul]
      rw [h4]
      all_goals ring
    rw [h5]
    have h6 : Real.sin (2 * α) ^ 2 + Real.cos (2 * α) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq (2 * α)
    nlinarith [sq_nonneg (Real.sin (2 * α) ^ 2 - 1), sq_nonneg (Real.cos (2 * α) ^ 2 - 1), sq_nonneg (Real.sin (2 * α) ^ 2 - Real.cos (2 * α) ^ 2), sq_nonneg (Real.sin (2 * α) * Real.cos (2 * α)), sq_nonneg (Real.sin (2 * α) - 0), sq_nonneg (Real.cos (2 * α) - 0), Real.sin_sq_add_cos_sq (2 * α)]

  rw [h1, h2]

  by_cases h8 : Real.sin (2 * α) = 0
  · -- when Real.sin (2 * α) = 0
    have h9 : Real.sin (2 * α) = 0 := h8
    have h11 : Real.cos (2 * α) ^ 2 = 1 := by
      have h8 : Real.sin (2 * α) ^ 2 + Real.cos (2 * α) ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * α)
      rw [show Real.sin (2 * α) ^ 2 = 0 by
        rw [h9]
        norm_num
      ] at h8
      nlinarith
    have h12 : -4 * (Real.cos (2 * α)) ^ 4 = -4 := by
      have h13 : Real.cos (2 * α) ^ 2 = 1 := h11
      have h14 : Real.cos (2 * α) ^ 4 = 1 := by
        calc
          Real.cos (2 * α) ^ 4 = (Real.cos (2 * α) ^ 2) ^ 2 := by ring
          _ = 1 ^ 2 := by rw [h13]
          _ = 1 := by norm_num
      linarith
    have h13 : -4 * (Real.sin (2 * α)) ^ 4 = 0 := by
      rw [show Real.sin (2 * α) = 0 by linarith [h8]]
      norm_num
    rw [h12, h13]
    norm_num [Real.tan_eq_sin_div_cos, h8, h11]
  · -- when Real.sin (2 * α) ≠ 0
    by_cases h18 : Real.cos (2 * α) = 0
    · -- when Real.cos (2 * α) = 0
      have h19 : Real.cos (2 * α) = 0 := h18
      have h20 : Real.sin (2 * α) ^ 2 = 1 := by
        have h8 : Real.sin (2 * α) ^ 2 + Real.cos (2 * α) ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * α)
        rw [show Real.cos (2 * α) ^ 2 = 0 by
          rw [h19]
          norm_num
        ] at h8
        nlinarith
      have h21 : -4 * (Real.cos (2 * α)) ^ 4 = 0 := by
        rw [show Real.cos (2 * α) = 0 by linarith [h19]]
        norm_num
      have h22 : -4 * (Real.sin (2 * α)) ^ 4 = -4 := by
        have h23 : Real.sin (2 * α) ^ 4 = 1 := by
          calc
            Real.sin (2 * α) ^ 4 = (Real.sin (2 * α) ^ 2) ^ 2 := by ring
            _ = 1 ^ 2 := by rw [h20]
            _ = 1 := by norm_num
        linarith
      rw [h21, h22]
      norm_num [Real.tan_eq_sin_div_cos, h19, h18, h8]
    · -- when Real.cos (2 * α) ≠ 0
      have h24 : Real.cos (2 * α) ≠ 0 := h18
      have h9 : Real.sin (2 * α) ^ 4 ≠ 0 := by
        intro h
        have h11 : Real.sin (2 * α) = 0 := by
          have h12 : Real.sin (2 * α) ^ 4 = 0 := by
            linarith
          simp at h12 ⊢
          all_goals tauto
        tauto
      have h16 : -4 * (Real.cos (2 * α)) ^ 4 / (-4 * (Real.sin (2 * α) ^ 4) ) = (Real.cos (2 * α) ^ 4) / (Real.sin (2 * α) ^ 4) := by
        have h17 : (Real.sin (2 * α)) ^ 4 ≠ 0 := h9
        field_simp
        all_goals ring
      rw [h16]
      have htan4 : 1 / (Real.tan (2 * α) ^ 4) = (Real.cos (2 * α) ^ 4) / (Real.sin (2 * α) ^ 4) := by
        have htan : Real.tan (2 * α) = Real.sin (2 * α) / Real.cos (2 * α) := by
          rw [Real.tan_eq_sin_div_cos]
        rw [htan]
        have h25 : Real.cos (2 * α) ≠ 0 := h24
        field_simp
      linarith [htan4]