import Mathlib

theorem calculus_17117 : Real.arccos (Real.sin 2) = 2 - Real.pi / 2 := by
  have h1 : Real.sin 2 = Real.cos (2 - Real.pi / 2) := by
    have h2 : Real.sin 2 = Real.cos (Real.pi / 2 - 2) := by 
      rw [← Real.cos_pi_div_two_sub]
    have h3 : Real.cos (Real.pi / 2 - 2) = Real.cos (2 - Real.pi / 2) := by 
      have h4 : Real.pi / 2 - 2 = - (2 - Real.pi / 2) := by 
        linarith [Real.pi_pos]
      rw [h4]
      rw [Real.cos_neg]
    rw [h2, h3]
  
  rw [h1]
  have h4 : 0 ≤ 2 - Real.pi / 2 := by 
    nlinarith [Real.pi_gt_three, Real.pi_lt_31416]

  have h5 : 2 - Real.pi / 2 ≤ Real.pi := by 
    nlinarith [Real.pi_gt_three, Real.pi_lt_31416]

  have h6 : Real.arccos (Real.cos (2 - Real.pi / 2)) = 2 - Real.pi / 2 := by 
    apply Real.arccos_cos
    all_goals 
      nlinarith [Real.pi_gt_three, Real.pi_lt_31416]
  
  exact h6