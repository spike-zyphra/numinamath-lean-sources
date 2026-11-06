import Mathlib

theorem algebra_21198 (x : ℝ) : (3 / 4 : ℝ) ^ x = 81 / 256 ↔ x = 4 := by
  constructor
  · -- Assume (3 / 4 : ℝ) ^ x = 81 / 256, prove x = 4
    intro h
    have h1 : x = (4 : ℝ) := by
      have h2 : (3 / 4 : ℝ) ^ (x : ℝ) = (81 / 256 : ℝ) := by 
        exact h
      have h3 : (81 / 256 : ℝ) = (3 / 4 : ℝ) ^ (4 : ℝ) := by 
        norm_num
      rw [h3] at h2 -- Now h2 becomes (3/4)^x = (3/4)^4
      have h4 : x = (4 : ℝ) := by
        apply_fun (Real.logb (3 / 4 : ℝ)) at h2
        have h5 : Real.logb (3 / 4 : ℝ) ((3 / 4 : ℝ) ^ (x : ℝ)) = (x : ℝ) := by 
          rw [Real.logb_rpow]
          all_goals norm_num
          all_goals linarith
        have h6 : Real.logb (3 / 4 : ℝ) ((3 / 4 : ℝ) ^ (4 : ℝ)) = (4 : ℝ) := by 
          rw [Real.logb_rpow]
          all_goals norm_num
          all_goals linarith
        linarith [h5, h6, h2]
      exact h4
    exact h1
  · -- Assume x = 4, prove (3 / 4 : ℝ) ^ x = 81 / 256
    intro h
    rw [h]
    norm_num