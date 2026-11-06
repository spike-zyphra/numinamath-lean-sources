import Mathlib

open Real

theorem algebra_179050 : tan (20 * π / 180) + 4 * sin (20 * π / 180) = sqrt 3 := by
  have h1 : cos (20 * π / 180) > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    · linarith [show 0 < 20 * π / 180 by nlinarith [Real.pi_pos]]
    · linarith [show 20 * π / 180 < Real.pi by nlinarith [Real.pi_pos, Real.pi_gt_three]]
  have h2 : tan (20 * π / 180) = sin (20 * π / 180) / cos (20 * π / 180) := by
    rw [tan_eq_sin_div_cos]
  have h3 : sin (20 * π / 180) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith [show 0 < 20 * π / 180 by nlinarith [Real.pi_pos]]
    · linarith [show 20 * π / 180 < Real.pi by nlinarith [Real.pi_pos, Real.pi_gt_three]]
  have heq : sin (20 * π / 180) / cos (20 * π / 180) + 4 * sin (20 * π / 180) = Real.sqrt 3 := by
    have heq2 : sin (20 * π / 180) / cos (20 * π / 180) + 4 * sin (20 * π / 180) =
        (sin (20 * π / 180) + 4 * sin (20 * π / 180) * cos (20 * π / 180) ) / cos (20 * π / 180) := by
      field_simp [h1]
    rw [heq2] at *
    have heq3 : sin (20 * π / 180) + 4 * sin (20 * π / 180) * cos (20 * π / 180) = Real.sqrt 3 * cos (20 * π / 180) := by
      have h5 : sin (40 * π / 180) = 2 * sin (20 * π / 180) * cos (20 * π / 180) := by
        have h7 : 40 * π / 180 = 2 * (20 * π / 180) := by ring
        rw [h7]
        rw [show sin (2 * (20 * π / 180)) = 2 * sin (20 * π / 180) * cos (20 * π / 180) by
          rw [Real.sin_two_mul]
        ]
        all_goals linarith
      have h8 : sin (40 * π / 180) = sin (π / 3 - 20 * π / 180) := by
        ring_nf 
      have h9 : sin (π / 3 - 20 * π / 180) = sin (π / 3) * cos (20 * π / 180) - cos (π / 3) * sin (20 * π / 180) := by
        rw [sin_sub]
      have h10 : sin (π / 3) = Real.sqrt 3 / 2 := by
        rw [sin_pi_div_three]
      have h11 : cos (π / 3) = 1 / 2 := by
        rw [cos_pi_div_three]
      have eq0 : sin (40 * π / 180) = Real.sqrt 3 / 2 * cos (20 * π / 180) - 1 / 2 * sin (20 * π / 180) := by
        rw [h8, h9, h10, h11]
      have eq1 : sin (20 * π / 180) + 4 * sin (20 * π / 180) * cos (20 * π / 180) = Real.sqrt 3 * cos (20 * π / 180) := by
        have eq3 : 4 * sin (20 * π / 180) * cos (20 * π / 180) = 2 * sin (40 * π / 180) := by
          linarith [h5]
        have eq4 : 2 * sin (40 * π / 180) = 2 * (Real.sqrt 3 / 2 * cos (20 * π / 180) - 1 / 2 * sin (20 * π / 180)) := by
          rw [eq0]
        have eq5 : sin (20 * π / 180) + 4 * sin (20 * π / 180) * cos (20 * π / 180) = Real.sqrt 3 * cos (20 * π / 180) := by
          rw [eq3, eq4]
          all_goals nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.pi_pos]
        exact eq5
      exact eq1
    have heq4 : (sin (20 * π / 180) + 4 * sin (20 * π / 180) * cos (20 * π / 180) ) / cos (20 * π / 180) = Real.sqrt 3 := by
      have h9 : cos (20 * π / 180) ≠ 0 := by linarith
      rw [heq3]
      field_simp [h9]
      <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.pi_pos]
    exact heq4
  rw [h2]
  exact heq