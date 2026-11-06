import Mathlib

theorem algebra_10683 {x y : ℝ} (eq₁ : (2 : ℝ) ^ x + 3 ^ y = 5) (eq₂ : (2 : ℝ) ^ (x + 2) + 3 ^ (y + 1) = 18) : (2 : ℝ) ^ x = 3 := by

  have eq6 : (2 : ℝ) ^ (x + 2) = (2 : ℝ) ^ x * (4 : ℝ) := by
    calc
      (2 : ℝ) ^ (x + 2) = (2 : ℝ) ^ x * (2 : ℝ) ^ (2 : ℝ) := by
        rw [← Real.rpow_add]
        all_goals norm_num
      _ = (2 : ℝ) ^ x * (4 : ℝ) := by
        norm_num
        all_goals norm_num

  have eq7 : (3 : ℝ) ^ (y + 1) = (3 : ℝ) ^ y * (3 : ℝ) := by
    calc
      (3 : ℝ) ^ (y + 1) = (3 : ℝ) ^ y * (3 : ℝ) ^ (1 : ℝ) := by
        rw [← Real.rpow_add]
        all_goals norm_num
      _ = (3 : ℝ) ^ y * (3 : ℝ) := by
        norm_num
        all_goals norm_num

  rw [eq6, eq7] at eq₂

  have eq₃ : (3 : ℝ) ^ y = (5 : ℝ) - (2 : ℝ) ^ x := by
    linarith

  rw [eq₃] at eq₂

  nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by linarith) x, Real.rpow_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by linarith) y, Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by linarith) (x + 2), Real.rpow_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by linarith) (y + 1)]