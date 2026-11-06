import Mathlib

theorem number_theory_237297 : ∃ N : ℕ, (Real.sqrt 3 - 1)^N = 4817152 - 2781184 * Real.sqrt 3 := by 
  use 16
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 3 - 1 : ℝ) ^ 2 = 4 - 2 * Real.sqrt 3 := by 
    nlinarith [h1, Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)]
  have h3 : (Real.sqrt 3 - 1 : ℝ) ^ 4 = (28 - 16 * Real.sqrt 3 : ℝ) := by
    calc
      (Real.sqrt 3 - 1 : ℝ) ^ 4
          = ((Real.sqrt 3 - 1 : ℝ) ^ 2) ^ 2 := by ring
      _   = (4 - 2 * Real.sqrt 3) ^ 2 := by 
        rw [h2]
      _   = (28 - 16 * Real.sqrt 3 : ℝ) := by
        nlinarith [h1, Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)]
  have h4 : (Real.sqrt 3 - 1 : ℝ) ^ 8 = (1552 - 896 * Real.sqrt 3 : ℝ) := by 
    calc
      (Real.sqrt 3 - 1 : ℝ) ^ 8
          = ((Real.sqrt 3 - 1 : ℝ) ^ 4) ^ 2 := by ring
      _   = (28 - 16 * Real.sqrt 3) ^ 2 := by 
        rw [h3]
      _   = (1552 - 896 * Real.sqrt 3 : ℝ) := by
        nlinarith [h1, Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)]
  have h5 : (Real.sqrt 3 - 1 : ℝ) ^ 16 = (4817152 - 2781184 * Real.sqrt 3 : ℝ) := by 
    calc
      (Real.sqrt 3 - 1 : ℝ) ^ 16
          = ((Real.sqrt 3 - 1 : ℝ) ^ 8) ^ 2 := by ring
      _   = (1552 - 896 * Real.sqrt 3) ^ 2 := by 
        rw [h4]
      _   = (4817152 - 2781184 * Real.sqrt 3 : ℝ) := by
        nlinarith [h1, Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)]
  exact h5