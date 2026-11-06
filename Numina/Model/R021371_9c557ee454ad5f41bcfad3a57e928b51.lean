import Mathlib

theorem algebra_243156 (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 3 + 3 * (x ^ 2 + x + Real.sin (Real.pi * x))) :
    f (1 - Real.pi) + f (Real.pi - 3) = -2 := by
  have h1 : f (1 - Real.pi) = (1 - Real.pi) ^ 3 + 3 * ((1 - Real.pi) ^ 2 + (1 - Real.pi) + Real.sin (Real.pi * (1 - Real.pi))) := by 
    rw [hf]
  have h2 : f (Real.pi - 3) = (Real.pi - 3) ^ 3 + 3 * ((Real.pi - 3) ^ 2 + (Real.pi - 3) + Real.sin (Real.pi * (Real.pi - 3))) := by 
    rw [hf]
  rw [h1, h2]
  
  have h3 : Real.sin (Real.pi * (1 - Real.pi)) = Real.sin (Real.pi ^ 2) := by
    have h4 : Real.pi * (1 - Real.pi) = Real.pi - Real.pi ^ 2 := by ring
    rw [h4]
    have h5 : Real.sin (Real.pi - Real.pi ^ 2) = Real.sin (Real.pi) * Real.cos (Real.pi ^ 2) - Real.cos (Real.pi) * Real.sin (Real.pi ^ 2) := by 
      rw [Real.sin_sub]
    rw [h5]
    have h6 : Real.sin (Real.pi) = 0 := Real.sin_pi
    have h7 : Real.cos (Real.pi) = -1 := Real.cos_pi
    rw [h6, h7]
    all_goals 
      nlinarith

  have h4 : Real.sin (Real.pi * (Real.pi - 3)) = - Real.sin (Real.pi ^ 2) := by
    have h5 : Real.pi * (Real.pi - 3) = Real.pi ^ 2 - 3 * Real.pi := by ring
    rw [h5]
    have h6 : Real.sin (Real.pi ^ 2 - 3 * Real.pi) = Real.sin (Real.pi ^ 2) * Real.cos (3 * Real.pi) - Real.cos (Real.pi ^ 2) * Real.sin (3 * Real.pi) := by 
      rw [Real.sin_sub]
    rw [h6]
    have h7 : Real.cos (3 * Real.pi) = -1 := by
      have h8 : 3 * Real.pi = Real.pi + 2 * Real.pi := by ring
      rw [h8]
      have h9 : Real.cos (Real.pi + 2 * Real.pi) = Real.cos (Real.pi) := by 
        rw [Real.cos_add, Real.cos_two_pi, Real.sin_two_pi]
        norm_num
      rw [h9]
      have h10 : Real.cos (Real.pi) = -1 := Real.cos_pi
      linarith
    have h8 : Real.sin (3 * Real.pi) = 0 := by
      have h9 : 3 * Real.pi = Real.pi + 2 * Real.pi := by ring
      rw [h9]
      have h10 : Real.sin (Real.pi + 2 * Real.pi) = Real.sin (Real.pi) := by 
        rw [Real.sin_add, Real.cos_two_pi, Real.sin_two_pi]
        norm_num
      rw [h10]
      have h11 : Real.sin (Real.pi) = 0 := Real.sin_pi
      linarith
    rw [h7, h8]
    all_goals 
      nlinarith
  
  have eq : (1 - Real.pi) ^ 3 + (Real.pi - 3) ^ 3 + 3 * ((1 - Real.pi) ^ 2 + (1 - Real.pi) + Real.sin (Real.pi * (1 - Real.pi))) + 3 * ((Real.pi - 3) ^ 2 + (Real.pi - 3) + Real.sin (Real.pi * (Real.pi - 3))) = -2 := by 
    rw [h3, h4]
    nlinarith [Real.pi_gt_three, Real.sin_sq_add_cos_sq (Real.pi * (1 - Real.pi)), Real.sin_sq_add_cos_sq (Real.pi * (Real.pi - 3)), Real.sin_sq_add_cos_sq (Real.pi ^ 2), Real.sin_sq_add_cos_sq (3 * Real.pi), sq_nonneg (Real.pi - 3), sq_nonneg (1 - Real.pi), sq_nonneg (Real.pi ^ 2 - 9), sq_nonneg (Real.pi * (1 - Real.pi)), sq_nonneg (Real.pi * (Real.pi - 3)), sq_nonneg (Real.pi ^ 2 - 3 * Real.pi)]
  nlinarith