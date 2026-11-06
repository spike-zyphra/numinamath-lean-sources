import Mathlib

theorem algebra_252724 (x : ℝ) : (5 : ℝ)^(2 * x + 1) - 3 * (5 : ℝ)^(2 * x - 1) = 550 ↔ x = 3 / 2 := by
  constructor
  · -- Assume left side, prove right side
    intro h
    have eq1 : (5 : ℝ) ^ (2 * x + 1) = 5 * (5 : ℝ) ^ (2 * x : ℝ) := by
      rw [show 2 * x + 1 = (2 * x : ℝ) + (1 : ℝ) by ring]
      rw [Real.rpow_add]
      norm_num
      all_goals linarith
    have eq2 : (5 : ℝ) ^ (2 * x - 1) = (5 : ℝ) ^ (2 * x : ℝ) / (5 : ℝ) := by
      rw [show 2 * x - 1 = (2 * x : ℝ) - (1 : ℝ) by ring]
      rw [Real.rpow_sub]
      field_simp
      all_goals linarith
    rw [eq1, eq2] at h
    have eq3 : (5 * (5 : ℝ) ^ (2 * x : ℝ) ) - 3 * ((5 : ℝ) ^ (2 * x : ℝ) / (5 : ℝ)) = (5 - (3 : ℝ)/5) * (5 : ℝ) ^ (2 * x : ℝ) := by
      field_simp
      <;> ring
    have eq4 : (5 - (3 : ℝ)/5) * (5 : ℝ) ^ (2 * x : ℝ) = (550 : ℝ) := by 
      linarith [h, eq3]
    have eq5 : (5 : ℝ) ^ (2 * x : ℝ) = (125 : ℝ) := by
      have pos1 : (5 : ℝ) ^ (2 * x : ℝ) > 0 := by positivity
      nlinarith
    have eq6 : (5 : ℝ) ^ (2 * x : ℝ) = (5 : ℝ) ^ (3 : ℝ) := by 
      rw [eq5]
      norm_num
    have eq7 : 2 * x = (3 : ℝ) := by 
      apply_fun (Real.logb (5 : ℝ)) at eq6
      have h1 : Real.logb (5 : ℝ) ((5 : ℝ) ^ (2 * x : ℝ)) = (2 * x : ℝ) := by 
        rw [Real.logb_rpow]
        all_goals norm_num
      have h2 : Real.logb (5 : ℝ) ((5 : ℝ) ^ (3 : ℝ)) = (3 : ℝ) := by 
        rw [Real.logb_rpow]
        all_goals norm_num
      rw [h1, h2] at eq6
      linarith 
    linarith 
  · -- Assume right side, prove left side
    intro h_eq
    rw [h_eq]
    have eq1 : 2 * (3 / 2 : ℝ) + 1 = (4 : ℝ) := by norm_num 
    have eq2 : 2 * (3 / 2 : ℝ) - 1 = (2 : ℝ) := by norm_num 
    rw [eq1, eq2] 
    norm_num