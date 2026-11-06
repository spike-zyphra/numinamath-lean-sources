import Mathlib

theorem algebra_20835 {x y : ℝ} (hx : (2 : ℝ)^(x + 1) = (4 : ℝ)^(x - 7)) (hy : (8 : ℝ)^(3 * y) = (16 : ℝ)^(-y + 13)) : x + y = 19 := by
  have eq1 : (4 : ℝ) ^ (x - 7 : ℝ) = (2 : ℝ) ^ (2 * (x - 7 : ℝ)) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring
    all_goals linarith
  rw [eq1] at hx
  have eq2 : x + 1 = 2 * (x - 7 : ℝ) := by
    apply_fun (Real.logb (2 : ℝ)) at hx
    have h2 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (x + 1 : ℝ)) = (x + 1 : ℝ) := by
      rw [Real.logb_rpow]
      all_goals linarith
    have h2' : Real.logb (2 : ℝ) ((2 : ℝ) ^ (2 * (x - 7 : ℝ)) ) = (2 * (x - 7 : ℝ) ) := by
      rw [Real.logb_rpow]
      all_goals linarith
    rw [h2, h2'] at hx
    linarith
  have hx15 : x = 15 := by
    linarith
  have eq3 : (8 : ℝ) ^ (3 * y : ℝ) = (2 : ℝ) ^ (9 * y : ℝ) := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith
  have eq4 : (16 : ℝ) ^ (-y + 13 : ℝ) = (2 : ℝ) ^ (4 * (-y + 13 : ℝ)) := by
    rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith
  rw [eq3, eq4] at hy
  have eq5 : 9 * y = 4 * (-y + 13 : ℝ) := by
    apply_fun (Real.logb (2 : ℝ)) at hy
    have h3 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (9 * y : ℝ)) = (9 * y : ℝ) := by
      rw [Real.logb_rpow]
      all_goals linarith
    have h4 : Real.logb (2 : ℝ) ((2 : ℝ) ^ (4 * (-y + 13 : ℝ)) ) = (4 * (-y + 13 : ℝ) ) := by
      rw [Real.logb_rpow]
      all_goals linarith
    rw [h3, h4] at hy
    linarith
  have hy4 : y = (4 : ℝ) := by
    linarith
  linarith [hx15, hy4]