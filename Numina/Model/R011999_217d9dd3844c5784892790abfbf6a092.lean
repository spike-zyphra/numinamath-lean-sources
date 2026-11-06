import Mathlib

theorem algebra_324718 (a b : ℤ) (h : a ^ 2 - b ^ 2 = 2003) : a ^ 2 + b ^ 2 = 2006005 := by
  have h1 : (a - b) * (a + b) = 2003 := by
    nlinarith [h]
  
  have h2 : (a - b) = 1 ∨ (a - b) = 2003 ∨ (a - b) = -1 ∨ (a - b) = -2003 := by
    have h4 : (a - b) ∣ 2003 := by 
      use (a + b)
      all_goals nlinarith [h1]
    
    have h3 : (a - b) ∣ 2003 := h4 
    have h5 : (a - b) ≤ 2003 := by 
      apply Int.le_of_dvd (by norm_num) h3 
    have h6 : (a - b) ≥ -2003 := by
      have h7 : -(a - b) ∣ 2003 := by
        exact Int.neg_dvd.2 h3 
      have h8 : -(a - b) ≤ 2003 := by
        apply Int.le_of_dvd (by norm_num) h7
      linarith [h8]
    interval_cases (a - b) <;> tauto

  rcases h2 with h2 | h2 | h2 | h2

  · -- case a - b = 1 
    have h3 : a + b = 2003 := by 
      nlinarith [h1, h2]
    have h4 : a = 1002 := by 
      linarith 
    have h5 : b = 1001 := by 
      linarith 
    rw [h4, h5] 
    norm_num

  · -- case a - b = 2003 
    have h3 : a + b = 1 := by 
      nlinarith [h1, h2]
    have h4 : a = 1002 := by 
      linarith 
    have h5 : b = -1001 := by 
      linarith 
    rw [h4, h5] 
    norm_num

  · -- case a - b = -1 
    have h3 : a + b = -2003 := by 
      nlinarith [h1, h2]
    have h4 : a = -1002 := by 
      linarith 
    have h5 : b = -1001 := by 
      linarith 
    rw [h4, h5] 
    norm_num

  · -- case a - b = -2003 
    have h3 : a + b = -1 := by 
      nlinarith [h1, h2]
    have h4 : a = -1002 := by 
      linarith 
    have h5 : b = 1001 := by 
      linarith 
    rw [h4, h5] 
    norm_num