import Mathlib

theorem algebra_172369 (x : ℝ) : abs (abs (abs (x - 2) + 3) - 4) = -3 * x - 9 ↔ x = -5 := by
  constructor
  · -- Assume left side, prove right side
    intro h_eq
    have h1 : -3 * x - 9 ≥ 0 := by
      linarith [abs_nonneg (abs (abs (x - 2) + 3) - 4), h_eq]
    have h2 : x ≤ -3 := by linarith
    have h3 : abs (x - 2) = 2 - x := by 
      rw [abs_of_neg]
      · linarith 
      all_goals linarith 
    have h4 : abs (abs (x - 2) + 3) = 5 - x := by 
      rw [h3]
      have h5 : (2 - x : ℝ) + 3 = 5 - x := by linarith 
      rw [h5]
      have h6 : 5 - x ≥ 0 := by 
        linarith 
      rw [abs_of_nonneg h6]
    have h7 : abs (abs (abs (x - 2) + 3) - 4) = 1 - x := by 
      rw [h4]
      have h8 : (5 - x : ℝ) - 4 = 1 - x := by linarith 
      rw [h8]
      have h9 : 1 - x ≥ 0 := by 
        linarith 
      rw [abs_of_nonneg h9]
    rw [h7] at h_eq 
    linarith 
  · -- Assume right side, prove left side 
    intro h_eq
    rw [h_eq]
    norm_num [abs_of_nonneg, abs_of_nonpos]