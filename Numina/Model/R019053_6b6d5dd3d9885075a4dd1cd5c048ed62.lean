import Mathlib

theorem algebra_21624 {x : ℝ} (hx : x > 0) (h : (x * Real.sqrt x) ^ ((1 : ℝ) / 3) = 7) :
    x = 49 := by
  have h1 : Real.sqrt x = (x) ^ (1 / 2 : ℝ) := by
    rw [show (x : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt x by simp [Real.sqrt_eq_rpow]]
  have h2 : x * Real.sqrt x = (x) ^ (3 / 2 : ℝ) := by
    have h3 : Real.sqrt x = (x) ^ (1 / 2 : ℝ) := h1
    rw [h3]
    have h4 : (x) ^ (3 / 2 : ℝ) = (x) ^ (1 : ℝ) * (x) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add]
      norm_num
      all_goals linarith
    rw [h4]
    simp [Real.rpow_one]
    all_goals linarith
  have h3 : (x * Real.sqrt x) ^ ((1 : ℝ) / 3) = ((x) ^ (3 / 2 : ℝ)) ^ ((1 : ℝ) / 3) := by
    rw [h2]
  have h4 : ((x) ^ (3 / 2 : ℝ)) ^ ((1 : ℝ) / 3) = (x) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h5 : Real.sqrt x = 7 := by
    have h6 : (x * Real.sqrt x) ^ ((1 : ℝ) / 3) = (x) ^ (1 / 2 : ℝ) := by
      rw [h3]
      rw [h4]
    rw [h6] at h
    have h7 : Real.sqrt x = (x) ^ (1 / 2 : ℝ) := by
      linarith [h1]
    have h8 : (x : ℝ) ^ (1 / 2 : ℝ) = 7 := by
      linarith [h]
    have h9 : Real.sqrt x = 7 := by
      rw [h7]
      linarith [h8]
    exact h9
  have h8 : x = 49 := by
    calc
      x = (Real.sqrt x) ^ 2 := by
        rw [Real.sq_sqrt]
        all_goals linarith
      _ = (7 : ℝ) ^ 2 := by
        rw [h5]
      _ = (49 : ℝ) := by
        norm_num
  linarith