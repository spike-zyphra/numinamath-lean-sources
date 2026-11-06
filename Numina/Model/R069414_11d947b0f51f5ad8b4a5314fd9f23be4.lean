import Mathlib

theorem algebra_97531 (x : ℝ) (hx : x > 0) : (x * Real.sqrt x) ^ ((1 : ℝ) / 3) = x ^ ((1 : ℝ) / 2) := by
  have h1 : Real.sqrt x = x ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
  have h2 : x * Real.sqrt x = (x : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [h1]
    -- Note: Using Real.rpow_add to handle exponent addition
    have h6 : x * (x ^ ((1 : ℝ) / 2 : ℝ)) = (x : ℝ) ^ ((3 : ℝ) / 2) := by
      have h3 : ((x : ℝ) ^ (1 : ℝ)) * ((x : ℝ) ^ ((1 : ℝ) / 2 : ℝ)) = (x : ℝ) ^ ((1 : ℝ) + ((1 : ℝ) / 2 : ℝ)) := by
        rw [← Real.rpow_add]
        all_goals norm_num
        all_goals linarith
      have h4 : (x : ℝ) ^ (1 : ℝ) = (x : ℝ) := by
        simp
      have h5 : ((x : ℝ) ^ ((1 : ℝ) / 2 : ℝ)) = (x : ℝ) ^ ((1 : ℝ) / 2 : ℝ) := by
        rfl
      calc
        x * (x ^ ((1 : ℝ) / 2 : ℝ)) = (x : ℝ) ^ (1 : ℝ) * (x ^ ((1 : ℝ) / 2 : ℝ)) := by rw [h4]
        _ = (x : ℝ) ^ (1 : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 2 : ℝ) := by rw [h5]
        _ = (x : ℝ) ^ ((1 : ℝ) + ((1 : ℝ) / 2 : ℝ)) := by rw [h3]
        _ = (x : ℝ) ^ ((3 : ℝ) / 2) := by norm_num
        _ = (x : ℝ) ^ ((3 : ℝ) / 2) := by rfl
    linarith [h6]
  rw [h2]
  have h3 : ((x : ℝ) ^ ((3 : ℝ) / 2 : ℝ)) ^ ((1 : ℝ) / 3) = (x : ℝ) ^ ((1 : ℝ) / 2) := by
    -- Note: Using Real.rpow_mul to handle nested exponentiation
    have h4 : ((x : ℝ) ^ ((3 : ℝ) / 2 : ℝ)) ^ ((1 : ℝ) / 3) = (x : ℝ) ^ (((3 : ℝ) / 2 : ℝ) * ((1 : ℝ) / 3)) := by
      rw [← Real.rpow_mul]
      all_goals norm_num
      all_goals linarith
    rw [h4]
    all_goals norm_num
    all_goals linarith
  rw [h3]
  all_goals linarith