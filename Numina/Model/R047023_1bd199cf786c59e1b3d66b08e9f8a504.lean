import Mathlib

theorem algebra_3619 {x : ℝ} (hx : x = 36 * Real.pi / 180) : Real.cos x = (1 + Real.sqrt 5) / 4 := by 
  rw [hx]
  have h1 : Real.cos (36 * Real.pi / 180) = Real.cos (Real.pi / 5) := by 
    ring_nf 
  have h2 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by 
    have h4 : Real.cos (Real.pi / 5) ^ 2 + Real.sin (Real.pi / 5) ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq (Real.pi / 5)
    have h5 : Real.sin (2 * (Real.pi / 5)) = 2 * Real.sin (Real.pi / 5) * Real.cos (Real.pi / 5) := by
      rw [Real.sin_two_mul]
    have h6 : Real.sin (3 * (Real.pi / 5)) = 3 * Real.sin (Real.pi / 5) - 4 * Real.sin (Real.pi / 5) ^ 3 := by 
      rw [Real.sin_three_mul]
    have h7 : 3 * Real.sin (Real.pi / 5) - 4 * Real.sin (Real.pi / 5) ^ 3 = 2 * Real.sin (Real.pi / 5) * Real.cos (Real.pi / 5) := by
      have h8 : Real.sin (3 * (Real.pi / 5)) = Real.sin (2 * (Real.pi / 5)) := by
        have h9 : 3 * (Real.pi / 5) + 2 * (Real.pi / 5) = Real.pi := by
          ring_nf
        have h10 : Real.sin (3 * (Real.pi / 5)) = Real.sin (Real.pi - 2 * (Real.pi / 5)) := by
          ring_nf
        have h11 : Real.sin (Real.pi - 2 * (Real.pi / 5)) = Real.sin (2 * (Real.pi / 5)) := by 
          rw [Real.sin_pi_sub]
        linarith [h10, h11, show Real.sin (3 * (Real.pi / 5)) = Real.sin (3 * (Real.pi / 5)) by rfl]
      rw [h6, h5] at h8
      linarith
    have h9 : Real.sin (Real.pi / 5) ≠ 0 := by
      have h1 : Real.pi / 5 > 0 := by 
        linarith [Real.pi_pos]
      have h2 : Real.sin (Real.pi / 5) > 0 := by 
        apply Real.sin_pos_of_pos_of_lt_pi 
        all_goals linarith [Real.pi_pos]
      linarith
    have h10 : 4 * Real.cos (Real.pi / 5) ^ 2 - 2 * Real.cos (Real.pi / 5) - 1 = 0 := by 
      have h11 : Real.sin (Real.pi / 5) ≠ 0 := h9
      have eq1 : 3 * Real.sin (Real.pi / 5) - 4 * Real.sin (Real.pi / 5) ^ 3 = 2 * Real.sin (Real.pi / 5) * Real.cos (Real.pi / 5) := by
        linarith [h7]
      have eq2 : 3 - 4 * Real.sin (Real.pi / 5) ^ 2 = 2 * Real.cos (Real.pi / 5) := by 
        have h12 : Real.sin (Real.pi / 5) ≠ 0 := h9 
        apply (mul_left_inj' h12).mp
        linarith 
      have eq3 : Real.sin (Real.pi / 5) ^ 2 = 1 - Real.cos (Real.pi / 5) ^ 2 := by 
        linarith [h4]
      rw [eq3] at eq2
      nlinarith
    have h11 : Real.cos (Real.pi / 5) > 0 := by 
      have h10 : Real.pi / 5 > 0 := by 
        linarith [Real.pi_pos]
      have h11 : Real.pi / 5 < Real.pi := by 
        linarith [Real.pi_pos]
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith
    have h12 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
      nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num), sq_nonneg (Real.cos (Real.pi / 5) - (1 + Real.sqrt 5) / 4)]
    linarith 
  -- Combine h1 and h2 to get the final result.
  have h3 : Real.cos (36 * Real.pi / 180) = (1 + Real.sqrt 5) / 4 := by 
    linarith [h1, h2]
  linarith [h3]