import Mathlib

theorem algebra_237912 : (4 * Real.cos (9 * Real.pi / 180) ^ 2 - 3) * (4 * Real.cos (27 * Real.pi / 180) ^ 2 - 3) * (4 * Real.cos (81 * Real.pi / 180) ^ 2 - 3) * (4 * Real.cos (243 * Real.pi / 180) ^ 2 - 3) = 1 := by

  have h1 : Real.cos (27 * Real.pi / 180) = 4 * Real.cos (9 * Real.pi / 180) ^ 3 - 3 * Real.cos (9 * Real.pi / 180) := by
    have h2 : 27 * Real.pi / 180 = 3 * (9 * Real.pi / 180) := by ring
    rw [h2]
    rw [Real.cos_three_mul]

  have h2 : Real.cos (81 * Real.pi / 180) = 4 * Real.cos (27 * Real.pi / 180) ^ 3 - 3 * Real.cos (27 * Real.pi / 180) := by
    have h3 : 81 * Real.pi / 180 = 3 * (27 * Real.pi / 180) := by ring
    rw [h3]
    rw [Real.cos_three_mul]

  have h3 : Real.cos (243 * Real.pi / 180) = 4 * Real.cos (81 * Real.pi / 180) ^ 3 - 3 * Real.cos (81 * Real.pi / 180) := by
    have h4 : 243 * Real.pi / 180 = 3 * (81 * Real.pi / 180) := by ring
    rw [h4]
    rw [Real.cos_three_mul]

  have h4 : Real.cos (729 * Real.pi / 180) = 4 * Real.cos (243 * Real.pi / 180) ^ 3 - 3 * Real.cos (243 * Real.pi / 180) := by
    have h5 : 729 * Real.pi / 180 = 3 * (243 * Real.pi / 180) := by ring
    rw [h5]
    rw [Real.cos_three_mul]

  have h5 : Real.cos (729 * Real.pi / 180) = Real.cos (9 * Real.pi / 180) := by
    have h6 : 729 * Real.pi / 180 = 9 * Real.pi / 180 + 4 * Real.pi := by ring
    rw [h6]
    have h7 : Real.cos (9 * Real.pi / 180 + 4 * Real.pi) = Real.cos (9 * Real.pi / 180) := by 
      have h8 : Real.cos (9 * Real.pi / 180 + 4 * Real.pi) = Real.cos (9 * Real.pi / 180 + 2 * Real.pi + 2 * Real.pi) := by ring
      rw [h8]
      have h9 : Real.cos (9 * Real.pi / 180 + 2 * Real.pi + 2 * Real.pi) = Real.cos (9 * Real.pi / 180 + 2 * Real.pi) := by
        rw [Real.cos_add, Real.cos_add]
        simp [Real.cos_two_pi, Real.sin_two_pi]
        all_goals ring_nf <;> simp [Real.cos_sq] <;> ring
      have h10 : Real.cos (9 * Real.pi / 180 + 2 * Real.pi) = Real.cos (9 * Real.pi / 180) := by 
        rw [Real.cos_add]
        simp [Real.cos_two_pi, Real.sin_two_pi]
        all_goals ring_nf <;> simp [Real.cos_sq] <;> ring
      rw [h9, h10]
      all_goals ring_nf <;> simp [Real.cos_sq] <;> ring
    exact h7
  -- compute each term
  have hcos1 : Real.cos (9 * Real.pi / 180) ≠ 0 := by
    have h1 : 0 < 9 * Real.pi / 180 := by 
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith [Real.pi_gt_three]
    have h2 : Real.cos (9 * Real.pi / 180) > 0 := by 
      apply Real.cos_pos_of_mem_Ioo 
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
      all_goals
        nlinarith [Real.pi_gt_three]
    linarith 
  have hcos2 : Real.cos (27 * Real.pi / 180) ≠ 0 := by
    have h1 : 0 < 27 * Real.pi / 180 := by 
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith [Real.pi_gt_three]
    have h2 : Real.cos (27 * Real.pi / 180) > 0 := by 
      apply Real.cos_pos_of_mem_Ioo 
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
      all_goals
        nlinarith [Real.pi_gt_three]
    linarith 
  have hcos3 : Real.cos (81 * Real.pi / 180) ≠ 0 := by
    have h1 : 0 < 81 * Real.pi / 180 := by 
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith [Real.pi_gt_three]
    have h2 : Real.cos (81 * Real.pi / 180) > 0 := by 
      apply Real.cos_pos_of_mem_Ioo 
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]
      all_goals
        nlinarith [Real.pi_gt_three]
    linarith 
  have hcos4 : Real.cos (243 * Real.pi / 180) ≠ 0 := by
    have h1 : Real.pi / 2 < 243 * Real.pi / 180 := by
      nlinarith [Real.pi_pos, Real.pi_gt_three]
    have h2 : Real.cos (243 * Real.pi / 180) < 0 := by
      apply Real.cos_neg_of_pi_div_two_lt_of_lt
      all_goals
        nlinarith [Real.pi_pos, Real.pi_gt_three]
    have h3 : Real.cos (243 * Real.pi / 180) ≠ 0 := by
      nlinarith 
    exact h3 
  -- express each term as div 
  have eq1 : (4 * Real.cos (9 * Real.pi / 180) ^ 2 - 3) = Real.cos (27 * Real.pi / 180) / Real.cos (9 * Real.pi / 180) := by
    field_simp [show Real.cos (9 * Real.pi / 180) ≠ 0 by
      exact hcos1 
    ]
    nlinarith [Real.cos_sq_add_sin_sq (9 * Real.pi / 180), Real.cos_sq_add_sin_sq (27 * Real.pi / 180), h1]
  
  have eq2 : (4 * Real.cos (27 * Real.pi / 180) ^ 2 - 3) = Real.cos (81 * Real.pi / 180) / Real.cos (27 * Real.pi / 180) := by 
    field_simp [show Real.cos (27 * Real.pi / 180) ≠ 0 by 
      exact hcos2 
    ]
    nlinarith [Real.cos_sq_add_sin_sq (27 * Real.pi / 180), Real.cos_sq_add_sin_sq (81 * Real.pi / 180), h2]

  have eq3 : (4 * Real.cos (81 * Real.pi / 180) ^ 2 - 3) = Real.cos (243 * Real.pi / 180) / Real.cos (81 * Real.pi / 180) := by 
    field_simp [show Real.cos (81 * Real.pi / 180) ≠ 0 by 
      exact hcos3 
    ]
    nlinarith [Real.cos_sq_add_sin_sq (81 * Real.pi / 180), Real.cos_sq_add_sin_sq (243 * Real.pi / 180), h3]

  have eq4 : (4 * Real.cos (243 * Real.pi / 180) ^ 2 - 3) = Real.cos (729 * Real.pi / 180) / Real.cos (243 * Real.pi / 180) := by 
    field_simp [show Real.cos (243 * Real.pi / 180) ≠ 0 by 
      exact hcos4 
    ]
    nlinarith [Real.cos_sq_add_sin_sq (243 * Real.pi / 180), Real.cos_sq_add_sin_sq (729 * Real.pi / 180), h4, h5]

  rw [eq1, eq2, eq3, eq4]
  field_simp [h5, hcos1, hcos2, hcos3, hcos4]
  <;> ring_nf <;> simp [Real.cos_sq] <;> ring 
  all_goals nlinarith [Real.pi_pos, Real.pi_gt_three]