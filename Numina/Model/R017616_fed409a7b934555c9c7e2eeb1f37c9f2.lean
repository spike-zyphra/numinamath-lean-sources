import Mathlib

theorem algebra_195852 : Real.logb 135 675 > Real.logb 45 75 := by
  have h1 : Real.logb 135 675 = (Real.log 675) / (Real.log 135) := by
    field_simp [Real.logb]

  have h2 : Real.logb 45 75 = (Real.log 75) / (Real.log 45) := by
    field_simp [Real.logb]

  -- Express logarithms in terms of logarithms of prime bases
  have h3 : Real.log 675 = 2 * Real.log 5 + 3 * Real.log 3 := by 
    calc 
      Real.log 675 = Real.log (5^2 * 3^3) := by norm_num 
      _ = Real.log (5^2) + Real.log (3^3) := by rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = 2 * Real.log 5 + 3 * Real.log 3 := by simp [Real.log_pow]

  have h4 : Real.log 135 = Real.log 5 + 3 * Real.log 3 := by 
    calc 
      Real.log 135 = Real.log (5 * 3^3) := by norm_num 
      _ = Real.log (5) + Real.log (3^3) := by rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = Real.log 5 + 3 * Real.log 3 := by simp [Real.log_pow]

  have h5 : Real.log 75 = 2 * Real.log 5 + Real.log 3 := by 
    calc
      Real.log 75 = Real.log (5^2 * 3) := by norm_num
      _ = Real.log (5^2) + Real.log (3) := by rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = 2 * Real.log 5 + Real.log 3 := by simp [Real.log_pow]

  have h6 : Real.log 45 = Real.log 5 + 2 * Real.log 3 := by 
    calc
      Real.log 45 = Real.log (5 * 3^2) := by norm_num 
      _ = Real.log (5) + Real.log (3^2) := by rw [Real.log_mul (by norm_num) (by norm_num)]
      _ = Real.log 5 + 2 * Real.log 3 := by simp [Real.log_pow]
  
  rw [h1, h2]
  rw [h3, h4, h5, h6]

  -- Show that the given inequality holds
  have h7 : Real.log 3 > 0 := by
    apply Real.log_pos 
    all_goals norm_num
  
  have h8 : Real.log 5 > 0 := by
    apply Real.log_pos 
    all_goals norm_num
  
  -- Prove that the difference of logarithm expressions is positive
  have h9 : (2 * Real.log 5 + 3 * Real.log 3) / (Real.log 5 + 3 * Real.log 3) - (2 * Real.log 5 + Real.log 3) / (Real.log 5 + 2 * Real.log 3) > 0 := by 
    have h10 : Real.log 5 + 3 * Real.log 3 > 0 := by 
      nlinarith [h7, h8]

    have h11 : Real.log 5 + 2 * Real.log 3 > 0 := by 
      nlinarith [h7, h8]
    
    have h12 : (2 * Real.log 5 + 3 * Real.log 3) / (Real.log 5 + 3 * Real.log 3) - (2 * Real.log 5 + Real.log 3) / (Real.log 5 + 2 * Real.log 3) =
        ((2 * Real.log 5 + 3 * Real.log 3) * (Real.log 5 + 2 * Real.log 3) - (2 * Real.log 5 + Real.log 3) * (Real.log 5 + 3 * Real.log 3)) / ((Real.log 5 + 3 * Real.log 3) * (Real.log 5 + 2 * Real.log 3)) := by 
      field_simp 
      <;> ring

    rw [h12]

    have h13 : ((2 * Real.log 5 + 3 * Real.log 3) * (Real.log 5 + 2 * Real.log 3) - (2 * Real.log 5 + Real.log 3) * (Real.log 5 + 3 * Real.log 3)) = 3 * ((Real.log 3) ^ 2) := by
      nlinarith

    rw [h13]

    have h14 : 3 * ((Real.log 3) ^ 2) > 0 := by 
      nlinarith [sq_pos_of_pos h7, sq_pos_of_pos h8]

    have h15 : (Real.log 5 + 3 * Real.log 3) * (Real.log 5 + 2 * Real.log 3) > 0 := by
      positivity

    apply div_pos
    · linarith [h14]
    · positivity

  linarith only [h9]