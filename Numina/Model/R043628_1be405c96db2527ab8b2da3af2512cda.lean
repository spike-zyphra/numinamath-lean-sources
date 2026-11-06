import Mathlib

open Real Set

theorem other_23710 : 20 / 60 < sin (20 * π / 180) ∧ sin (20 * π / 180) < 21 / 60 := by
  have h1 : 20 / 60 < sin (20 * π / 180) := by
    have h41 : sin (20 * π / 180) > 1 / 3 := by
      have h7 : sin (20 * π / 180) > 1 / 3 := by 
        have h11 : 0 < (20 * π / 180 : ℝ) := by 
          nlinarith [Real.pi_pos]
        have h12 : (20 * π / 180 : ℝ) < Real.pi / 2 := by 
          nlinarith [Real.pi_pos, Real.pi_gt_three]
        have h132 : sin (3 * (20 * π / 180)) = 3 * sin (20 * π / 180) - 4 * sin (20 * π / 180) ^ 3 := by 
          rw [sin_three_mul]
        have h155 : 3 * (20 * π / 180) = Real.pi / 3 := by 
          linarith [Real.pi_pos]
        have h133 : sin (3 * (20 * π / 180)) = Real.sqrt 3 / 2 := by 
          have h155 : 3 * (20 * π / 180) = Real.pi / 3 := by
            linarith [Real.pi_pos]
          rw [h155]
          exact sin_pi_div_three
        have h156 : Real.sqrt 3 / 2 = 3 * sin (20 * π / 180) - 4 * sin (20 * π / 180) ^ 3 := by 
          linarith [h132, h133]
        have h81 : sin (20 * π / 180) ^ 2 + cos (20 * π / 180) ^ 2 = 1 := Real.sin_sq_add_cos_sq (20 * π / 180)
        have h17 : sin (20 * π / 180) > 0 := by 
          apply sin_pos_of_pos_of_lt_pi
          linarith [Real.pi_pos]
          linarith [Real.pi_pos, Real.pi_gt_three]
        nlinarith [sq_nonneg (sin (20 * π / 180) - 1 / 3), sq_nonneg (cos (20 * π / 180) - Real.sqrt (1 - (1 / 3) ^ 2)), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_pos_of_pos h17, sq_nonneg (sin (20 * π / 180)^2 - (1 / 3)^2), sq_nonneg (cos (20 * π / 180) - Real.sqrt 3 / 2)]
      linarith
    linarith
  have h2 : sin (20 * π / 180) < 21 / 60 := by
    have h41 : sin (20 * π / 180) < 7 / 20 := by 
      have h7 : sin (20 * π / 180) < (20 * π / 180 : ℝ) := by
        apply sin_lt
        all_goals
          nlinarith [Real.pi_pos, Real.pi_gt_three]
      have h8 : (20 * π / 180 : ℝ) < (7 / 20 : ℝ) := by
        nlinarith [Real.pi_pos, Real.pi_lt_315, Real.pi_gt_three]
      linarith
    linarith
  constructor
  · linarith [h1]
  · linarith [h2]