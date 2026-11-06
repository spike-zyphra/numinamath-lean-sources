import Mathlib 

/-- Each person in Cambridge drinks a (possibly different) 12 ounce mixture of water and apple juice, where each drink has a positive amount of both liquids. Marc McGovern, the mayor of Cambridge, drinks $\frac{1}{6}$ of the total amount of water drunk and $\frac{1}{8}$ of the total amount of apple juice drunk. How many people are in Cambridge?-/

theorem Algebra_610094 {total_water : ℝ} {total_juice : ℝ} {total_liquids : ℝ} {num_peo : ℕ} 
  (h : total_liquids = total_water + total_juice) (h_marc : 1 / (6 : ℝ) * total_water + 1 / (8 : ℝ) * total_juice = 12)
  (h_total : 12 * num_peo = total_liquids) (hpos₁ : total_water > 0) (hpos₂ : total_juice > 0)
  : num_peo = 7 := by 
  --  The total amount of liquid drunk must be more than 6 times of the amount that Marc drinks. 
  have ineq₁ : total_liquids > 6 * 12 := by 
    calc 
      _ = total_water + total_juice := by rw [h]
      _ > 6 * (1 / (6 : ℝ) * total_water + 1 / (8 : ℝ) * total_juice ) := by linarith
      _ = 6 * 12 := by rw [h_marc]
  -- The total amount of liquid drunk must be less than 8 times of the amount that Marc drinks.
  have ineq₂ : total_liquids < 8 * 12 := by 
    calc 
      _ = total_water + total_juice := by rw [h]
      _ < 8 * (1 / (6 : ℝ) * total_water + 1 / (8 : ℝ) * total_juice ) := by linarith
      _ = 8 * 12 := by rw [h_marc]
  rw [←h_total] at ineq₁
  rw [←h_total] at ineq₂
  -- Therefore, the number of people in Cambridge is more than 6 but less than 8 , so it must be 7 .
  have ineq_aux : (num_peo : ℝ) > 6 := by 
    calc 
      _ = 12 * (num_peo : ℝ) / 12 := by simp 
      _ > 6 * (12 : ℝ) / 12 := by linarith
      _ = 6 := by norm_num
  have ineq_aux' : (num_peo : ℝ) < 8 := by 
    calc 
      _ = 12 * (num_peo : ℝ) / 12 := by simp 
      _ < 8 * (12 : ℝ) / 12 := by linarith
      _ = 8 := by norm_num
  norm_cast at ineq_aux
  norm_cast at ineq_aux'
  interval_cases num_peo
  rfl